// Copyright 2025. Silvano DAL ZILIO. All rights reserved.
// Use of this source code is governed by the MIT license
// that can be found in the LICENSE file.

package dcsolver_test

import (
	"fmt"

	"github.com/dalzilio/dcsolver"
)

// This example shows the basic usage of the package: create a new constraint
// system (DCS), add some variables and some constraints between them,
// then output a feasible solution.
func Example() {
	// Create a new DCS and add variables x, y and z.
	cg := dcsolver.NewDCS()
	cg.AddVars("x", "y", "z")

	// Each variable can be manipulated using its index. Since every system has
	// a reserved, default variable called "start" (with index 0), that stands
	// for the initial date, variables x, y, z have index 1, 2 and 3
	// respectively.
	fmt.Printf("list of variables: %v\n", cg.Names)

	// We can add constraints using one of the five supported operations: LTHAN
	// (less-than, <), LTEQ (less-tha or equal, ≤), EQ (equal, =), GTHAN
	// (greater-than, >), and GTEQ (greater-than or equal, ≥). By default, we
	// have the constraint that every variable, say x, is positive: x ≥ 0.
	//
	// For instance, to add the constraint z - x > 5 and z > y ≥ x (that can be
	// encoded as y - z < 0 and x - y ≤ 0):
	cg.Add(1, 3, dcsolver.GTHAN, 5)
	cg.Add(3, 2, dcsolver.LTHAN, 0)
	cg.Add(2, 1, dcsolver.LTEQ, 0)

	// The constraint z = 6 can be encoded as z - start = 6:
	cg.Add(0, 3, dcsolver.EQ, 6)

	// It is possible to print a human-readable representation of the system.
	fmt.Print(cg.PrintSystem())

	// You can check if the system is satisfiable by looking at the value of
	// [cg.SAT]. Since we use an incremental method, we stop updating a DCS as
	// soon as it is unsatisfiable. If SAT, you can output one feasible
	// solution. A valuation of the form "x: 1⁻" stands for the fact that the
	// value of x is of the form 1 ± ε, for ε a small positive value.
	fmt.Printf("Feasible solution: %s\n", cg.PrintFeasible())
	// Output:
	// list of variables: [start x y z]
	// 0 ≤ x
	// 0 ≤ y
	// 0 ≤ y - x
	// 6 ≤ z ≤ 6
	// 5 < z - x
	// 0 < z - y
	// Feasible solution: [x: 1⁻, y: 6⁻, z: 6]
}
