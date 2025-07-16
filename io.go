// Copyright 2025. Silvano DAL ZILIO. All rights reserved.
// Use of this source code is governed by the MIT license
// that can be found in the LICENSE file.

package dcsolver

import (
	"bytes"
	"fmt"
	"strconv"
)

func (cg CGraph) PrintFeasible() string {
	if !cg.SAT {
		return "UNSAT"
	}
	buf := bytes.Buffer{}
	buf.WriteString("[")
	for k, v := range cg.D {
		if k == 0 {
			continue
		}
		if k > 1 {
			buf.WriteString(", ")
		}
		diff := BSubstract(v, cg.D[0])
		buf.WriteString(fmt.Sprintf("%s: %d", cg.Names[k], diff.Value))
		if diff.Operation != LTEQ {
			buf.WriteRune('⁻')
		}
	}
	buf.WriteString("]")
	return buf.String()
}

func (cg CGraph) PrintSystem() string {
	buf := bytes.Buffer{}

	for k1 := range len(cg.Names) {
		if k1 == 0 {
			continue
		}
		for k2 := range k1 {
			// We print the constraint associated to k1 - k2, therefore the arc k2 -> k1.
			tpos1, sup := cg.edges(k2, k1)
			tpos2, inf := cg.edges(k1, k2)
			if tpos1 < 0 && tpos2 < 0 {
				continue
			}
			if tpos2 >= 0 {
				inf.Value = -inf.Value
				buf.WriteString(inf.PrintLowerBound())
				buf.WriteByte(' ')
			} else {
				buf.WriteString("    ")
			}
			buf.WriteString(cg.Names[k1])
			if k2 != 0 {
				buf.WriteString(" - ")
				buf.WriteString(cg.Names[k2])
			}
			if tpos1 >= 0 {
				buf.WriteByte(' ')
				buf.WriteString(sup.PrintUpperBound())
			}
			buf.WriteByte('\n')
		}
	}
	return buf.String()
}

func (cg CGraph) PrintSMTLIB() string {
	buf := bytes.Buffer{}
	for k, name := range cg.Names {
		if k == 0 {
			buf.WriteString("(declare-const start Real)\n")
			buf.WriteString("(assert (= start 0))\n")
			continue
		}
		buf.WriteString("(declare-const ")
		buf.WriteString(name)
		buf.WriteString(" Real)\n")
		buf.WriteString("(assert (>= ")
		buf.WriteString(name)
		buf.WriteString(" 0))\n")
	}

	buf.WriteRune('\n')

	// keys := set.Set{}
	// for k := range cg.Edges {
	// 	keys = set.Add(keys, k)
	// }

	for k := range len(cg.Names) {
		for _, e := range cg.Edges[k] {
			buf.WriteString("(assert (")
			if e.Length.Operation == LTEQ {
				buf.WriteString("<= (- ")
			} else {
				buf.WriteString("< (- ")
			}
			buf.WriteString(cg.Names[e.End])
			buf.WriteByte(' ')
			buf.WriteString(cg.Names[e.Start])
			buf.WriteString(") ")

			if l := e.Length.Value; l < 0 {
				buf.WriteString(fmt.Sprintf("(- %d)", -l))
			} else {
				buf.WriteString(strconv.Itoa(l))
			}
			buf.WriteString("))\n")
		}
	}
	return buf.String()
}
