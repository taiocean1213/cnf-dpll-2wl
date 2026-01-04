use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{BufRead, BufReader, Result};

type Literal = i32;
type Var = usize;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Edge {
    from: Var,
    to: Var,
}

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

struct PropagationState<'a> {
    assignments: &'a mut [Option<bool>],
    watch_lists: &'a mut Vec<Vec<usize>>,
    propagation_queue: &'a mut Vec<Literal>,
    trail: &'a mut Vec<usize>,
}

enum Decision {
    Single {
        var: Var,
        tried_polarity: bool,
        tried_both: bool,
    },
    Pair {
        var1: Var,
        var2: Var,
        tried_comb: u8,
        tried_all: bool,
    },
    Implication {
        edge: Edge,
    }, // Only one test needed per edge
}

pub struct Solver {
    pub clauses: Vec<Clause>,
    pub assignments: Vec<Option<bool>>,
    pub watch_lists: Vec<Vec<usize>>,
    trail: Vec<usize>,
    trail_lim: Vec<usize>,

    // Implication graph for 3-SAT clauses
    implications: HashMap<Edge, bool>, // proven necessary implications
    pending_implications: HashSet<Edge>, // candidates to test
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
            implications: HashMap::new(),
            pending_implications: HashSet::new(),
        };

        solver.initialize_watches();
        solver.extract_implication_candidates(); // Now safe: no mutable borrow during iteration
        Ok(solver)
    }

    #[inline]
    pub fn lit_to_var(lit: Literal) -> Var {
        lit.abs() as usize
    }

    #[inline]
    pub fn lit_to_idx(lit: Literal) -> usize {
        (lit.abs() as usize * 2) + (lit < 0) as usize
    }

    #[inline]
    fn make_lit(var: Var, polarity: bool) -> Literal {
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

        if literals.is_empty() || literals.len() > 3 {
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

    // Fixed: Collect candidates first, then insert mutably
    fn extract_implication_candidates(&mut self) {
        let mut candidates = HashSet::new();

        for clause in &self.clauses {
            if clause.literals.len() == 3 {
                let [a, b, c] = [clause.literals[0], clause.literals[1], clause.literals[2]];

                Self::try_add_candidate(&mut candidates, a, b, c);
                Self::try_add_candidate(&mut candidates, a, c, b);
                Self::try_add_candidate(&mut candidates, b, c, a);
            }
        }

        self.pending_implications = candidates;
    }

    fn try_add_candidate(
        candidates: &mut HashSet<Edge>,
        lit1: Literal,
        lit2: Literal,
        lit3: Literal,
    ) {
        // Look for pattern: (~x ∨ ~y ∨ z)  ==>  (x ∧ y) → z
        if lit3 > 0 && lit1 < 0 && lit2 < 0 {
            let from = Self::lit_to_var(-lit1);
            let to = Self::lit_to_var(lit3);
            candidates.insert(Edge { from, to });
        }
    }

    #[inline]
    pub fn get_literal_value(assignments: &[Option<bool>], lit: Literal) -> Option<bool> {
        assignments[Self::lit_to_var(lit)].map(|val| val == (lit > 0))
    }

    fn assign(assignments: &mut [Option<bool>], trail: &mut Vec<Var>, lit: Literal) -> bool {
        let var = Self::lit_to_var(lit);
        let polarity = lit > 0;
        match assignments[var] {
            None => {
                assignments[var] = Some(polarity);
                trail.push(var);
                true
            }
            Some(p) => p == polarity,
        }
    }

    fn undo_to_level(&mut self, level: usize) {
        if level >= self.trail_lim.len() {
            return;
        }
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
            trail: &mut self.trail,
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
                let w0_lit = w0;
                if !Self::assign(state.assignments, state.trail, w0_lit) {
                    return (true, true);
                }
                state.propagation_queue.push(w0_lit);
                (true, false)
            }
            _ => (true, false),
        }
    }

    fn pick_branching_pair(&self) -> (Option<Var>, Option<Var>) {
        let mut iter = self
            .assignments
            .iter()
            .enumerate()
            .skip(1)
            .filter(|(_, a)| a.is_none());
        let var1 = iter.next().map(|(i, _)| i);
        let var2 = iter.next().map(|(i, _)| i);
        (var1, var2)
    }

    fn assign_pair(&mut self, comb: u8, var1: Var, var2: Var) -> bool {
        let p = match comb {
            0 => [true, true],
            1 => [true, false],
            2 => [false, true],
            3 => [false, false],
            _ => return false,
        };
        let lit1 = Self::make_lit(var1, p[0]);
        if !Self::assign(&mut self.assignments, &mut self.trail, lit1) || !self.propagate(lit1) {
            return false;
        }
        let lit2 = Self::make_lit(var2, p[1]);
        if !Self::assign(&mut self.assignments, &mut self.trail, lit2) || !self.propagate(lit2) {
            return false;
        }
        true
    }

    // Test if (from → to) is forced: check if assuming from=T and to=F leads to conflict
    fn test_implication(&mut self, edge: Edge) -> bool {
        let from = edge.from;
        let to = edge.to;

        let save_lim = self.trail_lim.len();
        self.trail_lim.push(self.trail.len());

        // Assume from = true
        let lit_from = Self::make_lit(from, true);
        if !Self::assign(&mut self.assignments, &mut self.trail, lit_from)
            || !self.propagate(lit_from)
        {
            self.undo_to_level(save_lim);
            return false;
        }

        // Assume to = false
        let lit_to = Self::make_lit(to, false);
        let has_conflict = !Self::assign(&mut self.assignments, &mut self.trail, lit_to)
            || !self.propagate(lit_to);

        self.undo_to_level(save_lim);

        has_conflict // if conflict → implication is necessary
    }

    pub fn solve(&mut self) -> bool {
        if !self.initial_propagation() {
            return false;
        }

        let mut decision_stack: Vec<Decision> = Vec::new();

        loop {
            // Process pending implication tests
            if let Some(&edge) = self.pending_implications.iter().next() {
                self.pending_implications.remove(&edge);

                decision_stack.push(Decision::Implication { edge });
                self.trail_lim.push(self.trail.len());

                if self.test_implication(edge) {
                    self.implications.insert(edge, true);
                    // You could later use this to add (~from ∨ to) as a 2-clause if desired
                }
                continue;
            }

            let (var1_opt, var2_opt) = self.pick_branching_pair();
            if var1_opt.is_none() {
                return true; // All variables assigned → SAT
            }

            let var1 = var1_opt.unwrap();
            if let Some(var2) = var2_opt {
                decision_stack.push(Decision::Pair {
                    var1,
                    var2,
                    tried_comb: 0,
                    tried_all: false,
                });
                self.trail_lim.push(self.trail.len());
                if !self.assign_pair(0, var1, var2) {
                    if !self.backtrack(&mut decision_stack) {
                        return false;
                    }
                }
            } else {
                decision_stack.push(Decision::Single {
                    var: var1,
                    tried_polarity: true,
                    tried_both: false,
                });
                self.trail_lim.push(self.trail.len());
                let lit = Self::make_lit(var1, true);
                if !Self::assign(&mut self.assignments, &mut self.trail, lit)
                    || !self.propagate(lit)
                {
                    if !self.backtrack(&mut decision_stack) {
                        return false;
                    }
                }
            }
        }
    }

    fn backtrack(&mut self, stack: &mut Vec<Decision>) -> bool {
        while let Some(mut dec) = stack.pop() {
            let level = stack.len();
            match dec {
                Decision::Single {
                    var,
                    ref mut tried_polarity,
                    ref mut tried_both,
                } => {
                    if *tried_both {
                        self.undo_to_level(level);
                        continue;
                    }
                    self.undo_to_level(level);
                    *tried_polarity = !*tried_polarity;
                    *tried_both = true;
                    self.trail_lim.push(self.trail.len());
                    let lit = Self::make_lit(var, *tried_polarity);
                    let ok = Self::assign(&mut self.assignments, &mut self.trail, lit)
                        && self.propagate(lit);
                    stack.push(dec);
                    if ok {
                        return true;
                    }
                }
                Decision::Pair {
                    var1,
                    var2,
                    ref mut tried_comb,
                    ref mut tried_all,
                } => {
                    if *tried_all {
                        self.undo_to_level(level);
                        continue;
                    }
                    self.undo_to_level(level);
                    *tried_comb += 1;
                    if *tried_comb >= 4 {
                        *tried_all = true;
                        stack.push(dec);
                        continue;
                    }
                    self.trail_lim.push(self.trail.len());
                    let ok = self.assign_pair(*tried_comb, var1, var2);
                    stack.push(dec);
                    if ok {
                        return true;
                    }
                }
                Decision::Implication { .. } => {
                    // Only one test per implication — no retry
                    self.undo_to_level(level);
                    // Just continue searching
                }
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
            if !Self::assign(&mut self.assignments, &mut self.trail, l) || !self.propagate(l) {
                return false;
            }
        }
        true
    }

    pub fn print_model(&self) {
        for (i, &a) in self.assignments.iter().enumerate().skip(1) {
            if let Some(val) = a {
                print!("{}{} ", if val { "" } else { "-" }, i);
            }
        }
        println!("0");
    }
}
