# cnf-dpll-2wl
Created in [C++](https://cplusplus.com/) by [Petar Kukolj](https://github.com/qkolj), Remastered to [Rust](https://rust-lang.org/) by [Tai Alex](https://github.com/taiocean1213).


A [DPLL](https://en.wikipedia.org/wiki/DPLL_algorithm) SAT solver with [Two-Watched Literals (2WL)](https://www.researchgate.net/figure/The-2-watching-literal-method-The-watched-literals-are-are-x-6-and-x-8-Variable-x-6_fig3_220565739)  optimization in [Rust](https://rust-lang.org/).

---

## Usage

The solver expects a SAT problem encoded as a CNF formula in DIMACS file format as the first argument. It outputs either ```UNSAT``` if given formula is unsatisfiable, or ```SAT``` and valuation that satisfies given formula. Example usage:

```console
user@host:dpll-2wl$ cargo run examples/aim-50-1_6-yes1-4.cnf 
SAT
-1 2 -3 -4 -5 6 -7 -8 -9 10 11 -12 -13 14 15 16 -17 18 19 20 -21 22 23 24 25 -26 -27 
  ↪ -28 -29 -30 -31 32 -33 -34 35 36 -37 -38 39 40 -41 42 43 44 -45 46 47 -48 -49 50
user@host:dpll-2wl$ cargo run examples/hole6.cnf 
UNSAT

```

---

Some of the examples are taken from [here](https://people.sc.fsu.edu/~jburkardt/data/cnf/cnf.html).
