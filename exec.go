// Copyright 2025. Silvano DAL ZILIO. All rights reserved.
// Use of this source code is governed by the GPL license
// that can be found in the LICENSE file.

package dcsolver

import (
	"bytes"
	"fmt"
	"log"
	"os"
	"os/exec"
	"regexp"
	"strings"
)

// ExecZ3 executes the command z3 on a SMT script generated from cg. We assume
// that z3 is installed locally and can be resolved by [exec.LookPAth] (see
// documentation for [exec.Command]). We return true if the system is
// satisfiable, by a call to "(check-sat)", and false otherwise. When
// satisifiable, the second returned value is a string representation of the
// feasible solution, by a call to "(get-model)". Otherwise it is the error
// message returned by z3.
func (cg *CGraph) ExecZ3() (bool, string) {
	f, err := os.CreateTemp(".", "*.z3")
	if err != nil {
		log.Fatal(err)
	}

	fmt.Fprintln(f, cg.PrintSMTLIB())
	fmt.Fprintln(f)
	fmt.Fprintln(f, "(check-sat)")
	fmt.Fprintln(f, "(get-model)")

	// call Z3
	cmd := exec.Command("z3", f.Name())
	out := strings.Builder{}
	cmd.Stdout = &out
	err = cmd.Run()

	f.Close()
	os.Remove(f.Name())

	// An error means the system is unsat.
	if err != nil {
		return false, err.Error()
	}

	reg_z3 := regexp.MustCompile(`\(define-fun\s+(?P<varname>[[:alpha:]][[:word:]]*)\s+\(\) Real\s*(?P<value>\d+\.\d+|\([^\)]*\))\s*\)`)
	matches := reg_z3.FindAllStringSubmatch(out.String(), -1)
	output := map[string]string{}
	for _, s := range matches {
		output[s[1]] = s[2]
	}
	b := bytes.Buffer{}
	b.WriteString("[")
	for k, name := range cg.Names {
		if k == 0 {
			continue
		}
		if k != 1 {
			b.WriteString(", ")
		}
		b.WriteString(fmt.Sprintf("%s: %s", name, output[name]))
	}
	b.WriteString("]")
	return true, b.String()
}
