// Copyright 2025. Silvano DAL ZILIO. All rights reserved. Use of this source
// code is governed by the MIT license that can be found in the LICENSE file.

/*
Command dcsolve takes as input a file (with extension .smt) that describes a
difference systems using a subset of smt-lib syntax and check its satisfiability
using both the dcsolver package and the Z3 SMT solver. We also output a feasible
solution when the system is satisfiable.

# Usage

Usage of dcsolve:

	-h, --help              print this message
	-v, --verbose int[=1]   textual output (use -v=2 for more info) (default none)

files:

	infiles: input file is stdin when using -
	outfile: output is always on stdout
	errorfile: error are always printed on stderr

# Syntax

Supported smt-lib specifications are sequences of atoms of the following form.

  - (declare-const z Real)
  - (assert (op (- x y) n))
  - (assert (op (- x y) (- n)))
  - (assert (op x n))
  - (assert (op x (- n))

where:
  - op is one of <, <=, >, >=, or =
  - x, y are free constant symbols of sort Real,
  - n is a (positive) numeral.

We assume that every specification contains a declaration for the reserved
variable start, such as (declare-const start Real), used to represent the start
of time. This declaration is optional.

# Example of specification

Below is an example of valid specification, taken from example ex2.smt in the
testdata files:

	(declare-const z0 Real)
	(declare-const z1 Real)
	(declare-const z2 Real)

	(assert (<= (- z0 start) 2))
	(assert (< (- z1 z0) 3))
	(assert (<= (- z2 z1) 4))
	(assert (= z2 9))

When using option --verbose=1, dcsolver also outputs a textual representation of
the system.

	0 ≤ z0 ≤ 2
	0 ≤ z1
	    z1 - z0 < 3
	9 ≤ z2 ≤ 9
	    z2 - z1 ≤ 4

With the second level of verbosity (option -v=2), it outputs the smt-lib script
used for the [os/exec] call to Z3. This system is equivalent to the current
state of the DCS. Hence, some constraints may have been rewritten and some
redundant constraints may have been simplified.

	(declare-const start Real)
	(assert (= start 0))
	(declare-const z0 Real)
	(assert (>= z0 0))
	(declare-const z1 Real)
	(assert (>= z1 0))
	(declare-const z2 Real)
	(assert (>= z2 0))

	(assert (<= (- z0 start) 2))
	(assert (<= (- z2 start) 9))
	(assert (<= (- start z0) 0))
	(assert (< (- z1 z0) 3))
	(assert (<= (- start z1) 0))
	(assert (<= (- z2 z1) 4))
	(assert (<= (- start z2) (- 9)))
*/
package main
