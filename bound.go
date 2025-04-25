// Copyright 2025. Silvano DAL ZILIO. All rights reserved.
// Use of this source code is governed by the GPL license
// that can be found in the LICENSE file.

package dcsolver

import "fmt"

// Operation is the type of possible comparison operators. We only use < and ≤
// in our encoding into graph, and when printing a system, but allow the use of
// the other operators when defining the set of constraints. For instance, we
// allow equality constraints (that can be expressed as a conjunction of two
// comparison), but we do not support "distinct" (≠), since it would require a
// disjunction.
type Operation uint8

const (
	LTHAN Operation = iota // less-than, <
	LTEQ                   // less-than or equal, ≤
	EQ                     // equal, =
	GTHAN                  // greater-than, >
	GTEQ                   // greater-than or equal, ≥
)

// Bound is the type of bounds in a time interval.
type Bound struct {
	Operation
	Value int
}

func (b Bound) String() string {
	switch b.Operation {
	case LTEQ:
		return fmt.Sprintf("%d⁼", b.Value)
	default:
		return fmt.Sprintf("%d⁻", b.Value)
	}
}

// PrintLowerBound returns a textual representation of a bound used as a lower
// bound constraint, such as "4 <" or "5 ≤".
func (b Bound) PrintLowerBound() string {
	switch b.Operation {
	case LTEQ:
		return fmt.Sprintf("%d ≤", b.Value)
	default:
		return fmt.Sprintf("%d <", b.Value)
	}
}

// PrintUpperBound is the dual  of PrintLowerBound and returns a representation
// of a bound used as a lower bound constraint.
func (b Bound) PrintUpperBound() string {
	switch b.Operation {
	case LTEQ:
		return fmt.Sprintf("≤ %d", b.Value)
	default:
		return fmt.Sprintf("< %d", b.Value)
	}
}

// ReadOperation parses an operation names and returns the right value. It
// returns an error if the operator is not one of <, <=, >, >= or =.
func ReadOperation(s string) (Operation, error) {
	switch s {
	case "<":
		return LTHAN, nil
	case "<=":
		return LTEQ, nil
	case ">":
		return GTHAN, nil
	case ">=":
		return GTEQ, nil
	case "=":
		return EQ, nil
	default:
		return LTHAN, fmt.Errorf("%s is not a valid operator", s)
	}
}

/*****************************************************************************/

// BSubstract computes the diference, b1 - b2, between two bounds.
func BSubstract(b1, b2 Bound) Bound {
	diff := b1.Value - b2.Value
	if b1.Operation == LTHAN || b2.Operation == LTHAN {
		return Bound{LTHAN, diff}
	}
	return Bound{LTEQ, diff}
}

// BAdd returns the sum of two  bounds.
func BAdd(b1, b2 Bound) Bound {
	add := b1.Value + b2.Value
	if b1.Operation == LTHAN || b2.Operation == LTHAN {
		return Bound{LTHAN, add}
	}
	return Bound{LTEQ, add}
}

// BCompare returns an integer comparing two bounds. The result will be 0 if a
// and b are equal, negative if a < b, and positive otherwise. We return the
// difference between the bounds values, with some exceptions. We always return
// +1 when a and b have same values, but a is LTEQ whereas b is LTHAN. For
// intance, the bound ≤ 3 is considered strictly greater than < 3 with our
// choice. We return -1 in the symetric cases.
func BCompare(a, b Bound) int {
	if a.Value != b.Value {
		return a.Value - b.Value
	}
	if a.Operation == b.Operation {
		return 0
	}
	if a.Operation == LTHAN && b.Operation == LTEQ {
		return -1
	}
	return 1
}

// BMax returns the max of a and b.
func BMax(a, b Bound) Bound {
	if BCompare(a, b) <= 0 {
		return b
	}
	return a
}

// BMin returns the min of a and b.
func BMin(a, b Bound) Bound {
	if BCompare(a, b) <= 0 {
		return a
	}
	return b
}
