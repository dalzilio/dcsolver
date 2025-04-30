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
`cmd/dcsolve/main.go`.

```go
package main

import (
  "github.com/dalzilio/rudd"
  "math/big"
)

func main() {
  // create a new BDD with 6 variables, 10 000 nodes and a cache size of 5 000 (initially),
  // with an implementation based on the BuDDY approach
  bdd := rudd.New(6, Nodesize(10000), Cachesize(5000))
  // n1 == x2 & x3 & x5
  n1 := bdd.Makeset([]int{2, 3, 5})
  // n2 == x1 | !x3 | x4
  n2 := bdd.Or(bdd.Ithvar(1), bdd.NIthvar(3), bdd.Ithvar(4))
  // n3 == ∃ x2,x3,x5 . (n2 & x3)
  n3 := bdd.AndExist(n1, n2, bdd.Ithvar(3))
  // you can export a BDD in Graphviz's DOT format
  fmt.Printf("Number of sat. assignments: %s\n", bdd.Satcount(n3))
  fmt.Println(bdd.Stats())
  bdd.Dot(os.Stdout)
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

One main difference if our support for both strict and weak inequalities. Also,  Supporting strict constraints (meaning answering if the system is SAT for
rational/real values) is more difficult. Some solution is given in:

* Armando, A., Castellini, C., Giunchiglia, E., Maratea, M. (2005). [A SAT-Based
Decision Procedure for the Boolean Combination of Difference
Constraints](https://doi.org/10.1007/11527695_2). In Proc. of Theory and
Applications of Satisfiability Testing. SAT 2004. Lecture Notes in Computer
Science, vol 3542.

## Dependencies

The library has no dependencies outside the standard Go library. It uses Go
modules and has been tested with Go 1.24.

## License

This software is distributed under the [MIT
License](https://opensource.org/licenses/MIT). A copy of the license agreement
is found in the [LICENSE](./LICENSE.md) file.

## Authors

* **Silvano DAL ZILIO** - [LAAS/CNRS](https://www.laas.fr/)
