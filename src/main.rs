use std::env;
use std::process;

use cnf_dpll_2wl::Solver;

fn main() {
    let path = env::args().nth(1).expect("Usage: solver <file.cnf>");
    let mut solver = Solver::new(&path).unwrap_or_else(|e| {
        eprintln!("Error: {e}");
        process::exit(1);
    });

    if solver.solve() {
        println!("SAT");
        solver.print_model();
    } else {
        println!("UNSAT");
    }
}
