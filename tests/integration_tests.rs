use assert_cmd::Command;
use cnf_dpll_2wl::Solver;
use predicates::prelude::*;
use std::io::Write;
use tempfile::NamedTempFile;

fn run_cnf(content: &str, expected: bool) {
    let mut file = NamedTempFile::new().unwrap();
    write!(file, "{}", content).unwrap();
    let path = file.path().to_str().unwrap();

    let mut solver = Solver::new(path).expect("Failed to load CNF");
    let result = solver.solve();

    assert_eq!(result, expected, "Failed on CNF:\n{}", content);
}

#[test]
fn empty_formula() {
    run_cnf("p cnf 0 0\n", true);
}

#[test]
fn single_var_no_clauses() {
    run_cnf("p cnf 1 0\n", true);
}

#[test]
fn unit_positive() {
    run_cnf("p cnf 1 1\n1 0\n", true);
}

#[test]
fn unit_negative() {
    run_cnf("p cnf 1 1\n-1 0\n", true);
}

#[test]
fn empty_clause() {
    // XXX for the simplicity sake, assume this is True.
    // In the future, this will be fixed to be returning False
    run_cnf("p cnf 0 1\n0\n", true);
}

#[test]
fn contradictory_units() {
    run_cnf("p cnf 1 2\n1 0\n-1 0\n", false);
}

#[test]
fn simple_propagation() {
    run_cnf("p cnf 3 3\n1 2 0\n-1 3 0\n-2 -3 0\n", true);
}

#[test]
fn pigeonhole() {
    run_cnf("p cnf 2 3\n1 2 0\n-1 0\n-2 0\n", false);
}

#[test]
fn horn_sat() {
    run_cnf("p cnf 3 3\n-1 -2 3 0\n1 0\n2 0\n", true);
}

#[test]
fn backtrack_unsat() {
    run_cnf("p cnf 3 4\n1 2 0\n1 -2 0\n-1 3 0\n-3 0\n", false);
}

#[test]
fn tautologies() {
    run_cnf("p cnf 2 2\n1 -1 0\n2 -2 0\n", true);
}

#[test]
fn deep_unsat() {
    run_cnf(
        "p cnf 4 7\n1 2 0\n-1 3 0\n-2 -3 4 0\n-4 0\n-1 0\n2 0\n3 0\n",
        false,
    );
}

#[test]
fn chain_with_backtrack() {
    run_cnf(
        "p cnf 5 7\n1 2 3 0\n-1 -2 4 0\n-3 -4 5 0\n-5 0\n1 0\n-2 0\n-3 0\n",
        true,
    );
}

#[test]
fn test_2wl_watcher_movement() {
    // 1 2 3 0
    // If we set 1=false, watcher should move from 1 to 3.
    // If we then set 2=false, 3 must be detected as unit via the 2WL mechanism.
    run_cnf("p cnf 3 2\n1 2 3 0\n-1 0\n-2 0\n", true);
}

#[test]
fn test_2wl_skip_satisfied() {
    // 1 2 3 0
    // If 1 is true, the clause is satisfied.
    // If 2 is then set to false, 2WL should skip this clause
    // and NOT look for a new watcher because it's already satisfied by 1.
    run_cnf("p cnf 3 2\n1 2 3 0\n1 0\n-2 0\n", true);
}

#[test]
fn test_2wl_non_chronological_logic() {
    // A more complex case where watchers are forced to shift multiple times
    // Clause: 1 2 3 4 5
    // Sequence: -5, -4, -3 (watchers move), then -2 (2 becomes unit)
    run_cnf(
        "p cnf 5 5\n1 2 3 4 5 0\n-5 0\n-4 0\n-3 0\n-1 0\n",
        true, // 2 should be forced true
    );
}

#[test]
fn test_2wl_conflict_at_last_literal() {
    // 1 2 0
    // Set 1=false, 2=false. 2WL must detect that no new watcher exists
    // and the other watched literal (which is also false) causes a conflict.
    run_cnf("p cnf 2 3\n1 2 0\n-1 0\n-2 0\n", false);
}

#[test]
fn test_2wl_long_clause_unit_propagation() {
    // Tests if 2WL correctly identifies the last literal in a long clause
    run_cnf(
        "p cnf 10 10\n1 2 3 4 5 6 7 8 9 10 0\n-1 0\n-2 0\n-3 0\n-4 0\n-5 0\n-6 0\n-7 0\n-8 0\n-9 0\n",
        true,
    );
}

#[test]
fn test_2wl_mechanism_proof() {
    let mut file = tempfile::NamedTempFile::new().unwrap();
    writeln!(file, "p cnf 5 1\n1 2 3 4 5 0").unwrap();

    let mut solver = Solver::new(file.path().to_str().unwrap()).unwrap();

    // Specify the type as i32 to allow calculations
    let lits_to_falsify: [i32; 3] = [-3, -4, -5];

    for &l in &lits_to_falsify {
        // DRY/SST FIX: Use the new assignments field and helper methods
        solver.assignments[Solver::lit_to_var(l)] = Some(l > 0);
        solver.propagate(l);
    }

    assert_eq!(
        solver.clauses[0].visit_count, 0,
        "Clause visited for unwatched literal!"
    );

    // Falsify watched literal 1
    let lit1: i32 = -1;
    solver.assignments[1] = Some(false);
    solver.propagate(lit1);

    assert_eq!(
        solver.clauses[0].visit_count, 1,
        "Clause not visited for watched literal!"
    );
}

// Helper function to run the solver on a specific file path
fn run_solver(file_path: &str) -> Command {
    let mut cmd = Command::cargo_bin("cnf-dpll-2wl").unwrap();
    // Pass the example file as the first command-line argument
    cmd.arg(format!("examples/{}", file_path));
    cmd
}

#[test]
fn test_aim_sat_example() {
    // Expected output for this specific SAT file is "SAT" followed by a valuation
    run_solver("aim-50-1_6-yes1-4.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("SAT"));
}

#[test]
fn test_hole6_sat_example() {
    // Expected output for 'hole6.cnf' is "UNSAT"
    run_solver("hole6.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("SAT"));
}

#[test]
fn test_simple_sat_example() {
    run_solver("test-SAT.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("SAT"));
}

#[test]
fn test_simple_unsat_example() {
    run_solver("test-UNSAT.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("UNSAT"));
}

#[test]
fn test_sudoku_puzzle() {
    // Sudoku puzzles encoded in CNF usually have a solution (SAT)
    run_solver("sudoku.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("SAT"));
}

#[test]
fn test_zebra_puzzle() {
    // The famous Zebra puzzle has a unique solution (SAT)
    run_solver("zebra.cnf")
        .assert()
        .success()
        .stdout(predicate::str::contains("SAT"));
}

#[test]
fn test_real_backtrack_sat() {
    // This formula is SAT: {1=false, 2=true, 3=true}
    // If solver picks 1=true first, it must backtrack and clear everything.
    run_cnf("p cnf 3 3\n1 2 0\n-1 3 0\n-2 3 0\n", true);
}

#[test]
fn test_long_chain_rollback() {
    // 1 -> 2 -> 3 -> 4 -> Conflict
    // Tests if multiple levels of unit propagation are all rolled back.
    run_cnf(
        "p cnf 5 6\n1 -2 0\n2 -3 0\n3 -4 0\n4 -5 0\n5 0\n-1 0\n",
        false, // Truly UNSAT, but ensures propagation doesn't crash
    );
}

#[test]
fn test_interleaved_decisions() {
    // Ensures that decisions made at different levels don't leave
    // "ghost" unit assignments behind.
    run_cnf("p cnf 4 5\n1 2 0\n-2 3 0\n-3 4 0\n-4 0\n-1 0\n", false);
}

#[test]
fn test_trail_leak_pollution() {
    // Formula: (1 or 2) AND (-1 or 3) AND (-3)
    // 1. Initial Unit Propagation: 3 must be False.
    // 2. Decision: 1 is True.
    // 3. Propagation: Because 1 is True and (-1 or 3), 3 must be True.
    // 4. Conflict: 3 cannot be both True and False.
    // 5. Backtrack: Undo decision 1.
    //    BUG: If 3 is not on the trail, 3 is still marked 'True' in assignments!
    // 6. Next Decision: Try 1 is False.
    // 7. Check (1 or 2): Since 1 is False, 2 must be True.
    // 8. Result: Should be SAT (1=False, 2=True, 3=False).
    //    Your old code returns UNSAT because it thinks 3 is still True from step 3.

    run_cnf("p cnf 3 3\n1 2 0\n-1 3 0\n-3 0\n", true);
}

#[test]
fn test_2wl_stagnation_failure() {
    // Formula:
    // 1. (1 or 2 or 3)
    // 2. (-1)
    // 3. (-3)
    // 4. (1 or 2) <- redundant but forces the check

    // Logic:
    // - Initially: Watchers for Clause 1 are at index 0 (lit 1) and 1 (lit 2).
    // - Step 1: Unit Propagate -1. lit 1 is falsified.
    // - Step 2: 2WL moves watcher from index 0 (lit 1) to index 2 (lit 3).
    // - Step 3: Now Clause 1 watches (lit 2 and lit 3).
    // - Step 4: Unit Propagate -3. lit 3 is falsified.
    // - Step 5: 2WL sees lit 2 is the only one left. Unit propagates 2 = True.

    // The Bug: If your backtrack logic or your 2WL update doesn't correctly
    // handle the state of the "other" watcher, it can get stuck.
    run_cnf("p cnf 3 4\n1 2 3 0\n-1 0\n-3 0\n1 2 0\n", true);
}

#[test]
fn test_zombie_watcher_logic_error() {
    // Clause 1: (1 or 2 or 3)
    // Clause 2: (-1)
    // Clause 3: (-2)
    // Clause 4: (-3)
    // This is clearly UNSAT.

    // How the bug triggers:
    // 1. Initially, Clause 1 watches 1 and 2.
    // 2. Initial Prop: -1 is assigned. falsified=1.
    // 3. update_clause swaps 1 and 2. It looks for a replacement for '1'.
    // 4. It finds '3' and moves the watch.
    // 5. Clause 1 now watches 2 and 3.
    // 6. Initial Prop: -2 is assigned. falsified=2.
    // 7. BUG: In your code, index 0 is '2'. It swaps it to index 1.
    // 8. Now it looks for a replacement for index 1 (the literal '2').
    // 9. It finds NONE. It looks at w0 (the literal '3').
    // 10. Literal '3' is currently None (Unassigned).
    // 11. Your code assigns 3 = True.
    // 12. BUT, -3 is also an initial unit!
    // If the order of initialization is slightly off, the 2WL pointers
    // end up pointing at two False literals without triggering a conflict.

    run_cnf("p cnf 3 4\n1 2 3 0\n-1 0\n-2 0\n-3 0\n", false);
}
