use std::fs::File;
use std::io::{BufRead, BufReader, Result};

type Lit = i32;

pub struct Clause {
    pub lits: Vec<Lit>,
    pub w: [usize; 2],
    pub visit_count: usize,
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
        for l in BufReader::new(File::open(path)?)
            .lines()
            .map_while(Result::ok)
        {
            if l.starts_with('c') || l.is_empty() {
                continue;
            }
            if l.starts_with("p cnf") {
                n_vars = l
                    .split_whitespace()
                    .nth(2)
                    .unwrap_or("0")
                    .parse()
                    .unwrap_or(0);
                continue;
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
        let mut watch = vec![Vec::new(); (n_vars + 1) * 2];
        for (i, c) in clauses.iter().enumerate() {
            if !c.lits.is_empty() {
                watch[Self::idx(c.lits[c.w[0]])].push(i);
                if c.lits.len() > 1 {
                    watch[Self::idx(c.lits[c.w[1]])].push(i);
                }
            }
        }
        Ok(Self {
            clauses,
            assign: vec![None; n_vars + 1],
            watch,
        })
    }

    fn idx(l: Lit) -> usize {
        if l > 0 {
            l as usize * 2
        } else {
            (-l) as usize * 2 + 1
        }
    }

    fn val(&self, l: Lit) -> Option<bool> {
        self.assign[l.abs() as usize].map(|v| v == (l > 0))
    }

    pub fn propagate(&mut self, start: Lit) -> bool {
        let mut q = vec![start];
        while let Some(l) = q.pop() {
            let falsified = Self::idx(-l);
            let mut i = 0;
            while i < self.watch[falsified].len() {
                let cid = self.watch[falsified][i];
                self.clauses[cid].visit_count += 1;

                if self.clauses[cid].lits[self.clauses[cid].w[0]] == -l {
                    self.clauses[cid].w.swap(0, 1);
                }

                let w0 = self.clauses[cid].lits[self.clauses[cid].w[0]];
                if self.val(w0) == Some(true) {
                    i += 1;
                    continue;
                }

                let mut found = false;
                for j in 0..self.clauses[cid].lits.len() {
                    let cand = self.clauses[cid].lits[j];
                    if j != self.clauses[cid].w[0]
                        && j != self.clauses[cid].w[1]
                        && self.val(cand) != Some(false)
                    {
                        self.clauses[cid].w[1] = j;
                        self.watch[falsified].swap_remove(i);
                        self.watch[Self::idx(cand)].push(cid);
                        found = true;
                        break;
                    }
                }
                if found {
                    continue;
                }

                if self.val(w0) == Some(false) {
                    return false;
                }
                if self.val(w0).is_none() {
                    self.assign[w0.abs() as usize] = Some(w0 > 0);
                    q.push(w0);
                }
                i += 1;
            }
        }
        true
    }

    pub fn solve(&mut self) -> bool {
        if self.clauses.iter().any(|c| c.lits.is_empty()) {
            return false;
        }
        for idx in 0..self.clauses.len() {
            if self.clauses[idx].lits.len() == 1 {
                let lit = self.clauses[idx].lits[0];
                if self.val(lit) == Some(false) {
                    return false;
                }
                if self.val(lit).is_none() {
                    self.assign[lit.abs() as usize] = Some(lit > 0);
                    if !self.propagate(lit) {
                        return false;
                    }
                }
            }
        }
        self.solve_recursive()
    }

    fn solve_recursive(&mut self) -> bool {
        let var = match self
            .assign
            .iter()
            .enumerate()
            .skip(1)
            .find(|(_, a)| a.is_none())
        {
            Some((v, _)) => v,
            None => return true,
        };
        for pol in [true, false] {
            let (old_a, old_w) = (self.assign.clone(), self.watch.clone());
            self.assign[var] = Some(pol);
            if self.propagate(if pol { var as i32 } else { -(var as i32) })
                && self.solve_recursive()
            {
                return true;
            }
            self.assign = old_a;
            self.watch = old_w;
        }
        false
    }

    pub fn print_model(&self) {
        for (i, a) in self.assign.iter().enumerate().skip(1) {
            match a {
                Some(true) => print!("{i} "),
                Some(false) => print!("-{i} "),
                None => {}
            }
        }
        println!("0");
    }
}
