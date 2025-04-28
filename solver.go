// Copyright 2025. Silvano DAL ZILIO. All rights reserved.
// Use of this source code is governed by the GPL license
// that can be found in the LICENSE file.

// Package dcsolve implements a solver for linear systems of inequalities of the
// form x - y ≤ c or x - y < c, with c an integer constant, and z, y are
// positive, real-valued variables.
package dcsolver

import (
	"bytes"
	"fmt"
	"log"
	"strconv"

	"github.com/dalzilio/dcsolver/set"
)

type CGraph struct {
	SAT   bool          // true if system is satisfiable
	Names []string      // Name of variables; 0 is for the start variables.
	D     []Bound       // Feasible solution.
	Edges map[int][]Arc // Edges[i][j] = c represents the constraint zj - zi ≤ c.
}

type Arc struct {
	Start  int
	End    int
	Length Bound
}

// Add adds a constraint to the graph and returns false if the resulting system
// is not satisfiable.
func (cg *CGraph) Add(start int, end int, op Operation, n int) bool {
	if start == end {
		return true
	}
	switch op {
	case LTHAN, LTEQ:
		return cg.adds(Arc{Start: start, End: end, Length: Bound{Operation: op, Value: n}})
	case EQ:
		cg.adds(Arc{Start: start, End: end, Length: Bound{Operation: LTEQ, Value: n}})
		if !cg.SAT {
			return false
		}
		return cg.adds(Arc{Start: end, End: start, Length: Bound{Operation: LTEQ, Value: -n}})
	case GTHAN:
		return cg.adds(Arc{Start: end, End: start, Length: Bound{Operation: LTHAN, Value: -n}})
	case GTEQ:
		return cg.adds(Arc{Start: end, End: start, Length: Bound{Operation: LTEQ, Value: -n}})
	}
	log.Fatal("not possible")
	return false
}

// adds adds constraints of the form zj - zi ≤ a. We assume that i and j are
// different. We update the current graph with an arc i -> j of length a, if it
// did not exist yet, or if a.Length is smaller than the existing length. We
// return false as soon as the system is not satisfiable.
func (cg *CGraph) adds(a Arc) bool {
	tpos, length := cg.edges(a.Start, a.End)
	if tpos >= 0 && BCompare(a.Length, length) >= 0 {
		// We do not need to update the graph.
		return true
	}
	if tpos < 0 {
		cg.Edges[a.Start] = append(cg.Edges[a.Start], a)
	} else {
		cg.Edges[a.Start][tpos].Length = a.Length
	}

	// We apply Bellman-Ford but we only relax vertices which are the target of
	// edges from modified distances. Initially this is a.End. We can stop if
	// modified is empty, or if we find a.End again in the modified list
	// (meaning there is a negative cycle)
	updatelist := set.Set{}
	if udist := BAdd(cg.D[a.Start], a.Length); BCompare(udist, cg.D[a.End]) < 0 {
		cg.D[a.End] = udist
		updatelist = set.Set{a.End}
	}
	for len(updatelist) != 0 {
		v := updatelist[0]
		updatelist = updatelist[1:]
		for _, e := range cg.Edges[v] {
			if udist := BAdd(cg.D[v], e.Length); BCompare(udist, cg.D[e.End]) < 0 {
				cg.D[e.End] = udist
				updatelist = set.Add(updatelist, e.End)
			}
		}
		if set.Member(updatelist, a.Start) != -1 {
			// We have a negative cycle.
			cg.SAT = false
			return false
		}
	}
	return true
}

// edges returns the position where arc u -> v occurs in [cg.Edges], or -1 if it
// is absent. The second returned parameter is the length of this arc.
func (cg *CGraph) edges(u int, v int) (tpos int, length Bound) {
	l, found := cg.Edges[u]
	if !found {
		return -1, Bound{}
	}
	for k, a := range l {
		if a.End == v {
			return k, a.Length
		}
	}
	return -1, Bound{}
}

/*****************************************************************************/

func NewDCS() CGraph {
	return CGraph{
		SAT:   true,
		Names: []string{"start"},
		D:     []Bound{{Operation: LTEQ, Value: 0}},
		Edges: map[int][]Arc{0: {}},
	}
}

// AddVars adds new (top) variables with the constraint that the result is
// positive.
func (cg *CGraph) AddVars(names ...string) error {
	for _, name := range names {
		if name == "start" {
			return fmt.Errorf("start is a reserved variable name")
		}
		cg.Names = append(cg.Names, name)
		cg.D = append(cg.D, Bound{Operation: LTEQ, Value: 0})
		// We add the constraint 0 - zn ≤ 0
		cg.adds(Arc{Start: len(cg.Names) - 1, End: 0, Length: Bound{Operation: LTEQ, Value: 0}})
	}
	return nil
}

func (cg *CGraph) PrintFeasible() string {
	buf := bytes.Buffer{}

	for k, v := range cg.D {
		if k == 0 {
			buf.WriteString("[")
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

func (cg *CGraph) PrintSystem() string {
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
	buf.WriteString("\n")
	return buf.String()
}

func (cg *CGraph) PrintSMTLIB() string {
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

	keys := set.Set{}
	for k := range cg.Edges {
		keys = set.Add(keys, k)
	}

	for _, k := range keys {
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
