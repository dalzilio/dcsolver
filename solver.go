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
	"slices"
	"strconv"
	"unique"

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

// ACompare returns a negative value if e1 is less than e2, 0 if they have the
// same end points, and a positive value otherwise. We ony compare the Start and
// End points, because we have at most one arc for every pair of endpoints in
// each DCS.
func ACompare(e1, e2 Arc) int {
	if e1.Start == e2.Start {
		return e1.End - e2.End
	}
	return e1.Start - e2.Start
}

func NewDCS() CGraph {
	return CGraph{
		SAT:   true,
		Names: []string{"start"},
		D:     []Bound{{Operation: LTEQ, Value: 0}},
		Edges: map[int][]Arc{0: {}},
	}
}

// AddVars adds new (top) variables with the constraint that their value is
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

// AddNVar adds n new variables with names z(i) ... z(i+n), where i is the index
// of the first fresh variable. Like with AddVars, we add the constraint that
// thei value are all positive.
func (cg *CGraph) AddNVar(n int) {
	i := len(cg.Names) - 1
	for j := range n {
		cg.Names = append(cg.Names, "z"+strconv.Itoa(i+j))
		cg.D = append(cg.D, Bound{Operation: LTEQ, Value: 0})
		// We add the constraint 0 - zn ≤ 0
		cg.adds(Arc{Start: len(cg.Names) - 1, End: 0, Length: Bound{Operation: LTEQ, Value: 0}})
	}
}

// Add adds a constraint (end - start op n) to the graph, where op is one of {<,
// <=, =, >=, >}, and returns false if the resulting system is not satisfiable.
func (cg *CGraph) Add(start int, end int, op Operation, n int) bool {
	if start == end {
		return true
	}
	switch op {
	case LTHAN, LTEQ:
		return cg.adds(Arc{Start: start, End: end, Length: Bound{Operation: op, Value: n}})
	case EQ:
		cg.adds(Arc{Start: start, End: end, Length: Bound{Operation: LTEQ, Value: n}})
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
// return false as soon as the system is not satisfiable. We sort edges by
// increasing order according to ACompare.
func (cg *CGraph) adds(a Arc) bool {
	index, found := slices.BinarySearchFunc(cg.Edges[a.Start], a, ACompare)
	if found {
		b := cg.Edges[a.Start][index]
		if BCompare(b.Length, a.Length) <= 0 {
			// The old bound is less than the new one. We do not need to update
			// the graph.
			return true
		}
		cg.Edges[a.Start][index] = a
	} else {
		cg.Edges[a.Start] = slices.Insert(cg.Edges[a.Start], index, a)
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

// Clone returns a deep copy of a DCS graph.
func (cg *CGraph) Clone() CGraph {
	result := CGraph{
		SAT:   cg.SAT,
		Names: slices.Clone(cg.Names),
		D:     slices.Clone(cg.D),
		Edges: make(map[int][]Arc, len(cg.Edges)),
	}
	for k, v := range cg.Edges {
		result.Edges[k] = slices.Clone(v)
	}
	return result
}

// Equal reports if two systems have the same set of edges, compared using ==.
// Note that two DCS with different Names slices can be equal.
func Equal(cg1, cg2 CGraph) bool {
	if len(cg1.Names) != len(cg2.Names) || len(cg1.Edges) != len(cg2.Edges) {
		return false
	}
	for k := range len(cg1.Names) {
		if !slices.Equal(cg1.Edges[k], cg2.Edges[k]) {
			return false
		}
	}
	return true
}

/*****************************************************************************/

// Key is a unique identifier for each DCS
type Key unique.Handle[string]

func (dk Key) Value() string {
	return unique.Handle[string](dk).Value()
}

// Unique creates a unique key from a DBM
func (cg *CGraph) Unique() Key {
	buf := bytes.Buffer{}
	n := len(cg.Names)
	buf.WriteString(strconv.Itoa(n))
	buf.WriteByte('\n')
	for k := range n {
		for _, a := range cg.Edges[k] {
			buf.WriteString(strconv.Itoa(a.End))
			buf.WriteByte(' ')
			if a.Length.Operation == LTEQ {
				buf.WriteByte('=')
			} else {
				buf.WriteByte('<')
			}
			buf.WriteString(strconv.Itoa(a.Length.Value))
		}
		buf.WriteByte('\n')
	}
	return Key(unique.Make(buf.String()))
}
