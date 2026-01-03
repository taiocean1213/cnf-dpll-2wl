use std::fs::File;
use std::io::{BufRead, BufReader, Result};

type Literal = i32;

pub struct Clause {
    pub literals: Vec<Literal>,
    pub watched_indices: [usize; 2],
    pub visit_count: usize,
}

impl Clause {
    fn find_replacement_watch(&self, assignments: &[Option<bool>]) -> Option<usize> {
        self.literals
            .iter()
            .enumerate()
            .position(|(idx, &candidate)| {
                idx != self.watched_indices[0]
                    && idx != self.watched_indices[1]
                    && Solver::get_literal_value(assignments, candidate) != Some(false)
            })
    }
}

/// Added trail to state so unit assignments can be tracked for backtracking
struct PropagationState<'a> {
    assignments: &'a mut [Option<bool>],
    watch_lists: &'a mut Vec<Vec<usize>>,
    propagation_queue: &'a mut Vec<Literal>,
    trail: &'a mut Vec<usize>,
}

struct Decision {
    var: usize,
    tried_polarity: bool,
    tried_both: bool,
}

pub struct Solver {
    pub clauses: Vec<Clause>,
    pub assignments: Vec<Option<bool>>,
    pub watch_lists: Vec<Vec<usize>>,
    trail: Vec<usize>,
    trail_lim: Vec<usize>,
}

impl Solver {
    pub fn new(path: &str) -> Result<Self> {
        let mut variable_count = 0;
        let mut clauses = Vec::new();
        let lines = BufReader::new(File::open(path)?)
            .lines()
            .map_while(Result::ok);

        for line in lines {
            Self::parse_dimacs_line(line, &mut variable_count, &mut clauses);
        }

        let mut solver = Self {
            clauses,
            assignments: vec![None; variable_count + 1],
            watch_lists: vec![Vec::new(); (variable_count + 1) * 2],
            trail: Vec::new(),
            trail_lim: Vec::new(),
        };

        solver.initialize_watches();
        Ok(solver)
    }

    #[inline]
    pub fn lit_to_var(lit: Literal) -> usize {
        lit.abs() as usize
    }

    #[inline]
    pub fn lit_to_idx(lit: Literal) -> usize {
        (lit.abs() as usize * 2) + (lit < 0) as usize
    }

    #[inline]
    fn make_lit(var: usize, polarity: bool) -> Literal {
        if polarity { var as i32 } else { -(var as i32) }
    }

    fn parse_dimacs_line(line: String, variable_count: &mut usize, clauses: &mut Vec<Clause>) {
        if line.starts_with('c') || line.is_empty() {
            return;
        }
        if line.starts_with("p cnf") {
            *variable_count = line
                .split_whitespace()
                .nth(2)
                .and_then(|s| s.parse().ok())
                .unwrap_or(0);
            return;
        }
        let literals: Vec<Literal> = line
            .split_whitespace()
            .filter_map(|s| s.parse().ok())
            .take_while(|&val| val != 0)
            .collect();

        if literals.is_empty() {
            return;
        }

        let len = literals.len();
        clauses.push(Clause {
            literals,
            watched_indices: [0, 1.min(len.saturating_sub(1))],
            visit_count: 0,
        });
    }

    fn initialize_watches(&mut self) {
        for (id, c) in self.clauses.iter().enumerate() {
            if let Some(&lit0) = c.literals.get(c.watched_indices[0]) {
                self.watch_lists[Self::lit_to_idx(lit0)].push(id);
            }
            if c.literals.len() > 1 {
                let lit1 = c.literals[c.watched_indices[1]];
                self.watch_lists[Self::lit_to_idx(lit1)].push(id);
            }
        }
    }

    #[inline]
    pub fn get_literal_value(assignments: &[Option<bool>], lit: Literal) -> Option<bool> {
        assignments[Self::lit_to_var(lit)].map(|val| val == (lit > 0))
    }

    fn assign(&mut self, lit: Literal) {
        let var = Self::lit_to_var(lit);
        if self.assignments[var].is_none() {
            self.assignments[var] = Some(lit > 0);
            self.trail.push(var);
        }
    }

    fn undo_to_level(&mut self, level: usize) {
        let pos = self.trail_lim[level];
        while self.trail.len() > pos {
            let var = self.trail.pop().unwrap();
            self.assignments[var] = None;
        }
        self.trail_lim.truncate(level);
    }

    pub fn propagate(&mut self, satisfied_lit: Literal) -> bool {
        let mut queue = vec![satisfied_lit];
        while let Some(l) = queue.pop() {
            if !self.process_watch_list(l, &mut queue) {
                return false;
            }
        }
        true
    }

    fn process_watch_list(&mut self, satisfied_lit: Literal, queue: &mut Vec<Literal>) -> bool {
        let falsified_idx = Self::lit_to_idx(-satisfied_lit);
        let mut affected = std::mem::take(&mut self.watch_lists[falsified_idx]);
        let mut conflict = false;

        let mut state = PropagationState {
            assignments: &mut self.assignments,
            watch_lists: &mut self.watch_lists,
            propagation_queue: queue,
            trail: &mut self.trail, // Pass trail here
        };

        affected.retain(|&cid| {
            if conflict {
                return true;
            }
            let (keep, is_conflict) =
                Self::update_clause(&mut self.clauses[cid], -satisfied_lit, cid, &mut state);
            conflict = is_conflict;
            keep
        });

        self.watch_lists[falsified_idx].extend(affected);
        !conflict
    }

    fn update_clause(
        c: &mut Clause,
        falsified: Literal,
        cid: usize,
        state: &mut PropagationState,
    ) -> (bool, bool) {
        c.visit_count += 1;
        if c.literals[c.watched_indices[0]] == falsified {
            c.watched_indices.swap(0, 1);
        }

        let w0 = c.literals[c.watched_indices[0]];
        if Self::get_literal_value(state.assignments, w0) == Some(true) {
            return (true, false);
        }

        if let Some(j) = c.find_replacement_watch(state.assignments) {
            c.watched_indices[1] = j;
            state.watch_lists[Self::lit_to_idx(c.literals[j])].push(cid);
            return (false, false);
        }

        match Self::get_literal_value(state.assignments, w0) {
            Some(false) => (true, true),
            None => {
                // FIXED: Record the unit assignment on the trail
                let var = Self::lit_to_var(w0);
                state.assignments[var] = Some(w0 > 0);
                state.trail.push(var);
                state.propagation_queue.push(w0);
                (true, false)
            }
            _ => (true, false),
        }
    }

    fn pick_branching_variable(&self) -> Option<usize> {
        self.assignments
            .iter()
            .enumerate()
            .skip(1)
            .find(|(_, a)| a.is_none())
            .map(|(i, _)| i)
    }

    pub fn solve(&mut self) -> bool {
        if !self.initial_propagation() {
            return false;
        }

        let mut decision_stack: Vec<Decision> = Vec::new();

        loop {
            let var = self.pick_branching_variable();
            if var.is_none() {
                return true;
            }

            let current_var = var.unwrap();
            decision_stack.push(Decision {
                var: current_var,
                tried_polarity: true,
                tried_both: false,
            });

            self.trail_lim.push(self.trail.len());
            let lit = Self::make_lit(current_var, true);
            self.assign(lit);

            if !self.propagate(lit) {
                if !self.backtrack(&mut decision_stack) {
                    return false;
                }
            }
        }
    }

    fn backtrack(&mut self, stack: &mut Vec<Decision>) -> bool {
        while let Some(mut decision) = stack.pop() {
            if decision.tried_both {
                self.undo_to_level(stack.len());
                continue;
            }

            self.undo_to_level(stack.len());

            decision.tried_polarity = !decision.tried_polarity;
            decision.tried_both = true;

            let lit = Self::make_lit(decision.var, decision.tried_polarity);
            self.trail_lim.push(self.trail.len());
            self.assign(lit);

            let ok = self.propagate(lit);
            stack.push(decision);

            if ok {
                return true;
            }
        }
        false
    }

    fn initial_propagation(&mut self) -> bool {
        if self.clauses.iter().any(|c| c.literals.is_empty()) {
            return false;
        }

        let units: Vec<Literal> = self
            .clauses
            .iter()
            .filter(|c| c.literals.len() == 1)
            .map(|c| c.literals[0])
            .collect();

        for l in units {
            match Self::get_literal_value(&self.assignments, l) {
                Some(false) => return false,
                Some(true) => continue,
                None => {
                    self.assign(l);
                    if !self.propagate(l) {
                        return false;
                    }
                }
            }
        }
        true
    }

    pub fn print_model(&self) {
        for (i, &a) in self.assignments.iter().enumerate().skip(1) {
            if let Some(val) = a {
                print!("{}{i} ", if val { "" } else { "-" });
            }
        }
        println!("0");
    }
}
