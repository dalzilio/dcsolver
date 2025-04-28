// Copyright 2025. Silvano DAL ZILIO. All rights reserved.
// Use of this source code is governed by the GPL license
// that can be found in the LICENSE file.

package main

import (
	"fmt"
	"log"
	"os"
	"os/exec"
	"regexp"
	"strings"

	"github.com/dalzilio/dcsolver"
)

func callz3(cg dcsolver.CGraph) {
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

	// an error means the system is unsat
	if err != nil {
		fmt.Print("\n*** Z3: UNSAT ***\n\n")
		return
	}

	fmt.Print("\n*** Z3: SAT ***\n\n")
	reg_z3 := regexp.MustCompile(`\(define-fun\s+(?P<varname>[[:alpha:]][[:word:]]*)\s+\(\) Real\s*(?P<value>\d+\.\d+|\([^\)]*\))\s*\)`)
	matches := reg_z3.FindAllStringSubmatch(out.String(), -1)
	output := map[string]string{}
	for _, s := range matches {
		output[s[1]] = s[2]
	}
	fmt.Print("[")
	for k, name := range cg.Names {
		if k == 0 {
			continue
		}
		if k != 1 {
			fmt.Print(", ")
		}
		fmt.Printf("%s: %s", name, output[name])
	}
	fmt.Print("]\n")
}
