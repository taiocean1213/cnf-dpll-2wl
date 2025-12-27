use std::fs::File;
use std::io::{BufRead, BufReader, Result};

type Lit = i32;

pub struct Clause {
    pub lits: Vec<Lit>,
    pub w: [usize; 2],
    pub visit_count: usize,
}

impl Clause {
    /// High-level logic: search for a literal that isn't falsified and isn't currently watched.
    fn find_replacement_watch(&self, assign: &[Option<bool>]) -> Option<usize> {
        self.lits.iter().enumerate().position(|(j, &cand)| {
            j != self.w[0] && j != self.w[1] && Solver::get_val(assign, cand) != Some(false)
        })
    }
}

/// A context object to solve the "Long Parameter List" smell.
/// Bundles mutable references needed during propagation.
struct StateRef<'a> {
    assign: &'a mut [Option<bool>],
    watch: &'a mut Vec<Vec<usize>>,
    q: &'a mut Vec<Lit>,
}

pub struct Solver {
    pub clauses: Vec<Clause>,
    pub assign: Vec<Option<bool>>,
    pub watch: Vec<Vec<usize>>,
}

impl Solver {
    pub fn new(path: &str) -> Result<Self> {
        let mut n_vars = 0;
        let mut clauses = Vec::new();
        let lines = BufReader::new(File::open(path)?)
            .lines()
            .map_while(Result::ok);

        for line in lines {
            Self::parse_line(line, &mut n_vars, &mut clauses);
        }

        let mut solver = Self {
            clauses,
            assign: vec![None; n_vars + 1],
            watch: vec![Vec::new(); (n_vars + 1) * 2],
        };

        solver.init_watches();
        Ok(solver)
    }

    fn parse_line(l: String, n_vars: &mut usize, clauses: &mut Vec<Clause>) {
        if l.starts_with('c') || l.is_empty() {
            return;
        }
        if l.starts_with("p cnf") {
            *n_vars = l
                .split_whitespace()
                .nth(2)
                .and_then(|s| s.parse().ok())
                .unwrap_or(0);
            return;
        }

        let lits: Vec<Lit> = l
            .split_whitespace()
            .filter_map(|s| s.parse().ok())
            .take_while(|&x| x != 0)
            .collect();

        let len = lits.len();
        clauses.push(Clause {
            lits,
            w: [0, 1.min(len.saturating_sub(1))],
            visit_count: 0,
        });
    }

    fn init_watches(&mut self) {
        for (i, c) in self.clauses.iter().enumerate() {
            c.lits
                .get(c.w[0])
                .iter()
                .for_each(|&&l| self.watch[Self::idx(l)].push(i));
            if c.lits.len() > 1 {
                self.watch[Self::idx(c.lits[c.w[1]])].push(i);
            }
        }
    }

    #[inline]
    fn idx(l: Lit) -> usize {
        (l.abs() as usize * 2) + (l < 0) as usize
    }

    #[inline]
    fn get_val(assign: &[Option<bool>], l: Lit) -> Option<bool> {
        assign[l.abs() as usize].map(|v| v == (l > 0))
    }

    pub fn propagate(&mut self, start: Lit) -> bool {
        let mut q = vec![start];
        while let Some(l) = q.pop() {
            if !self.process_watch_list(l, &mut q) {
                return false;
            }
        }
        true
    }

    fn process_watch_list(&mut self, lit: Lit, q: &mut Vec<Lit>) -> bool {
        let falsified_idx = Self::idx(-lit);
        let mut watch_list = std::mem::take(&mut self.watch[falsified_idx]);
        let mut conflict = false;

        let mut state = StateRef {
            assign: &mut self.assign,
            watch: &mut self.watch,
            q,
        };

        watch_list.retain(|&cid| {
            if conflict {
                return true;
            }
            let (keep, is_conflict) =
                Self::update_clause(&mut self.clauses[cid], -lit, cid, &mut state);
            conflict = is_conflict;
            keep
        });

        self.watch[falsified_idx].extend(watch_list);
        !conflict
    }

    /// Returns (keep_in_current_watch_list, is_conflict)
    fn update_clause(
        c: &mut Clause,
        falsified: Lit,
        cid: usize,
        state: &mut StateRef,
    ) -> (bool, bool) {
        c.visit_count += 1;
        if c.lits[c.w[0]] == falsified {
            c.w.swap(0, 1);
        }

        let w0 = c.lits[c.w[0]];
        if Self::get_val(state.assign, w0) == Some(true) {
            return (true, false);
        }

        if let Some(j) = c.find_replacement_watch(state.assign) {
            c.w[1] = j;
            state.watch[Self::idx(c.lits[j])].push(cid);
            return (false, false);
        }

        match Self::get_val(state.assign, w0) {
            Some(false) => (true, true),
            None => {
                state.assign[w0.abs() as usize] = Some(w0 > 0);
                state.q.push(w0);
                (true, false)
            }
            _ => (true, false),
        }
    }

    pub fn solve(&mut self) -> bool {
        if self.clauses.iter().any(|c| c.lits.is_empty()) {
            return false;
        }

        let units: Vec<Lit> = self
            .clauses
            .iter()
            .filter(|c| c.lits.len() == 1)
            .map(|c| c.lits[0])
            .collect();

        if units.into_iter().any(|l| !self.apply_initial_unit(l)) {
            return false;
        }

        self.solve_recursive()
    }

    fn apply_initial_unit(&mut self, lit: Lit) -> bool {
        match Self::get_val(&self.assign, lit) {
            Some(false) => false,
            Some(true) => true,
            None => {
                self.assign[lit.abs() as usize] = Some(lit > 0);
                self.propagate(lit)
            }
        }
    }

    fn solve_recursive(&mut self) -> bool {
        let var = self
            .assign
            .iter()
            .enumerate()
            .skip(1)
            .find(|(_, a)| a.is_none())
            .map(|(v, _)| v);

        let Some(v) = var else {
            return true;
        };

        [true, false]
            .into_iter()
            .any(|pol| self.try_assignment(v, pol))
    }

    fn try_assignment(&mut self, var: usize, pol: bool) -> bool {
        let (old_a, old_w) = (self.assign.clone(), self.watch.clone());
        self.assign[var] = Some(pol);

        let lit = if pol { var as i32 } else { -(var as i32) };
        if self.propagate(lit) && self.solve_recursive() {
            return true;
        }

        self.assign = old_a;
        self.watch = old_w;
        false
    }

    pub fn print_model(&self) {
        self.assign.iter().enumerate().skip(1).for_each(|(i, &a)| {
            a.iter()
                .for_each(|&val| if val { print!("{i} ") } else { print!("-{i} ") });
        });
        println!("0");
    }
}
