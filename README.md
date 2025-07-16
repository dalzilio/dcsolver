# DCSolver

DCSolver is a pure Go library for checking the satisfiability of Difference
Constraints Systems (DCS), meaning a conjunction of linear inequalities of the
form `x - y ≤ a` or `x - y < b`, where `x` and `y` are positive, real-valued
variables, and `a` and `b` are integer constants.

We also provide a command-line tool, called `dcsolve`, used to showcase how to
use our API. The tool can be used to check the satisfiability of a DCS expressed
using a restricted subset of SMT-LIB syntax.

## Usage

You can find an example in the code of the dcsolve command, see
`cmd/dcsolve/main.go`. The following example shows the basic usage of the
package: create a new constraint system (DCS), add some variables and some
constraints between them, then output a feasible solution. You can also look at
the documentation example on the pkgsite for this package.

```go
package main

import (
 "fmt"
 "github.com/dalzilio/dcsolver"
)

func main() {
 // Create a new DCS and add variables x and y.
 cg := dcsolver.NewDCS()
 cg.AddVars("x", "y")

 // Each variable can be manipulated using its index. Since every system has
 // a reserved, default variable called "start" (with index 0), that stands
 // for the initial date, variables x and y have index 1 and 2 respectively.
 fmt.Printf("list of variables: %v\n", cg.Names)

 // We can add constraints using one of the five supported operations: LTHAN
 // (less-than, <), LTEQ (less-tha or equal, ≤), EQ (equal, =), GTHAN
 // (greater-than, >), and GTEQ (greater-than or equal, ≥). By default, we
 // have the constraint that every variable, say x, is positive: x ≥ 0.
 //
 // A call to Add(i, j, op, n) updates the DCS by adding the constraint 
 // Names[j] - Names[i] op n. For instance, to add the constraint y ≥ x + 1 
 // (that can be encoded as y - x GTEQ 1):
 cg.Add(1, 2, dcsolver.GTEQ, 1)

 // It is possible to print a human-readable representation of the system.
 fmt.Print(cg.PrintSystem())
 
 // You can check if the system is satisfiable by looking at the value of
 // cg.SAT. If true, it is possible to output one feasible
 // solution. A valuation of the form "x: 1⁻" stands for the fact that the
 // value of x is of the form 1 ± ε, for ε a small positive value.
 if (cg.SAT) {
   fmt.Printf("Feasible solution: %s\n", cg.PrintFeasible())
 }
}
```

## About

We follow an approach described by Pratt, where satisfiability is reduced to the
problem of checking the absence of negative cycles in a graph where variables
are node, and there is an edge from `y` to `x` of length `c`to represent the
constraint `x - y < c`.

We consider a special vertex for the starting date, associated with the
(reserved) variable `start`. Hence, we can encode constraints of the form `x ≤
b` or `x > a`, using relations of the form `x - start ≤ b` and `0 - start < a`,
respectively.

We borrowed some ideas from the following work, that defines an incremental
method for solving this kind of problem. At the moment, we follow a simpler
approach based on a simplified version of Bellman-Ford algorithm.

* Ramalingam, G., Song, J., Joskowicz, L. et al. [Solving Systems of Difference
Constraints Incrementally](https://doi.org/10.1007/PL00009261). Algorithmica 23,
261–275 (1999).

One main difference if our support for both strict and weak inequalities. Also,
supporting strict constraints (meaning answering if the system is SAT for
rational/real values) is more difficult. Some solution is given in:

* Armando, A., Castellini, C., Giunchiglia, E., Maratea, M. (2005). [A SAT-Based
Decision Procedure for the Boolean Combination of Difference
Constraints](https://doi.org/10.1007/11527695_2). In Proc. of Theory and
Applications of Satisfiability Testing. SAT 2004. Lecture Notes in Computer
Science, vol 3542.

## Dependencies

The library has no dependencies outside the standard Go library. It uses Go
modules and has been tested with Go 1.24.

For function ExecZ3, we assume that the command z3 is installed locally and can
be resolved by exec.LookPath.

## License

This software is distributed under the [MIT
License](https://opensource.org/licenses/MIT). A copy of the license agreement
is found in the [LICENSE](./LICENSE.md) file.

## Authors

* **Silvano DAL ZILIO** - [LAAS/CNRS](https://www.laas.fr/)
