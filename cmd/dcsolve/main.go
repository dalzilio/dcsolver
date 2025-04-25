// Copyright 2025. Silvano DAL ZILIO. All rights reserved.
// Use of this source code is governed by the GPL license
// that can be found in the LICENSE file.

package main

import (
	"bufio"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"time"

	"github.com/dalzilio/dcsolver"
	flag "github.com/spf13/pflag"
)

// Command dcsolve takes a difference systems expressed using a subset of
// smt-lib syntax, with atoms of the following form.
//
//   - (declare-const z0 Int)
//   - (assert (op (- x y) n))
//   - (assert (op (- x y) (- n)))
//   - (assert (op x n))
//
// where:
//   - op is one of <, <=, >, >=, or =
//   - x, y are free constant symbols of sort Int,
//   - n is a (positive) numeral.
//
// We assume that every specification starts with the line (declare-const start
// Int), where start is a reserved symbol, used to represent the start of time.

// goreleaser provides a default list of custom ldflags (see `go link -X
// importpath.name=value`):
//
//   - -X main.version={{.Version}} : Current Git tag (the v prefix is stripped) or the name of the snapshot, if you're using the --snapshot flag
//   - -X main.commit={{.Commit}} : Current git commit SHA
//   - -X main.date={{.Date}} : Date in the RFC3339 format
//   - -X main.builtBy=goreleaser'.
var (
	version = "dev"
	commit  = "none"
	date    = "2025-01-12T17:00:00Z"
)

func main() {
	var flaghelp = flag.BoolP("help", "h", false, "print this message")
	var flagv = flag.IntP("verbose", "v", 0, "textual output (use -v=2 for more info)")
	flag.Lookup("verbose").NoOptDefVal = "1"
	flag.Lookup("verbose").DefValue = "none"
	var flagversion = flag.Bool("version", false, "print version number and generation date")

	flag.CommandLine.SortFlags = false

	// Format the creation date to a shorter form.
	date_compiled, err := time.Parse(time.RFC3339, date)
	if err != nil {
		panic(err)
	}
	date = date_compiled.Format(time.DateOnly)

	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "dcsolve version %s (%s) -- %s -- LAAS/CNRS\n", version, commit, date)
		fmt.Fprintf(os.Stderr, "Usage of %s:\n", os.Args[0])
		flag.PrintDefaults()
		fmt.Fprintf(os.Stderr, "\nfiles:\n")
		fmt.Fprintf(os.Stderr, "   infiles: input file is stdin when using -\n")
		fmt.Fprintf(os.Stderr, "   outfile: output is always on stdout\n")
		fmt.Fprintf(os.Stderr, "   errorfile: error are always printed on stderr\n")
	}

	flag.Parse()
	N := len(flag.Args())

	if *flaghelp {
		flag.Usage()
		os.Exit(0)
	}

	if *flagversion {
		fmt.Printf("dcsolve version %s (%s) -- %s -- LAAS/CNRS\n", version, commit, date)
		os.Exit(0)
	}

	switch {
	case (N > 1):
		log.Fatal("should have exactly one smt-lib file")
	case flag.NArg() == 0:
		log.Fatal("should have exactly one smt-lib file")
	}

	var osfile *os.File
	if flag.Arg(0) == "-" {
		osfile = os.Stdin
	} else {
		fileExtension := filepath.Ext(flag.Arg(0))
		if fileExtension != ".smt" {
			log.Fatal("File extension should be .smt")
		}
		osfile, err = os.Open(flag.Arg(0))
	}
	if err != nil {
		log.Fatal("error opening file:", err)
	}
	defer osfile.Close()

	// We parse the input file and populate our constraint graph.
	cg := dcsolver.NewDCS()
	lines := 0
	names := map[string]int{"start": 0}
	var matches []string

	reg_varname := regexp.MustCompile(`^\(declare-const\s+(?P<varname>[[:alpha:]][[:word:]]*)\s+Int\s*\)`)
	reg_assertop := regexp.MustCompile(`^\(assert\s+\((?P<op>[=><][=]?)\s+(?P<rest>.*)\)\)$`)
	reg_twos := regexp.MustCompile(`^(?P<varname>[[:alpha:]][[:word:]]*)\s+(?P<cst>\d+)\s*$`)
	reg_op1 := regexp.MustCompile(`\(-\s*(?P<varname1>[[:alpha:]][[:word:]]*)\s+(?P<varname2>[[:alpha:]][[:word:]]*)\s*\)\s+(?P<n>\d+)`)
	reg_op2 := regexp.MustCompile(`\(-\s*(?P<varname1>[[:alpha:]][[:word:]]*)\s+(?P<varname2>[[:alpha:]][[:word:]]*)\s*\)\s+\(-\s+(?P<n>\d+)\s*\)`)

	scanner := bufio.NewScanner(osfile)
	for scanner.Scan() {
		if !cg.SAT {
			break
		}

		line := scanner.Text()
		lines++

		// We skip blank lines.
		if len(line) == 0 {
			continue
		}

		// And also comments.
		if strings.HasPrefix(line, ";") {
			continue
		}

		//   - (declare-const z0 Int)
		matches = reg_varname.FindStringSubmatch(line)
		if len(matches) > 0 {
			if *flagv > 0 {
				fmt.Printf(";; variable \"%s\" added\n", matches[1])
			}
			if matches[1] == "start" {
				continue
			}
			if _, found := names[matches[1]]; found {
				log.Fatalf("line %d, var %s redefined in %s", lines, matches[1], matches[0])
			}
			names[matches[1]] = len(cg.Names)
			cg.AddVar(matches[1])
			continue
		}

		//   - (assert (op ...))
		matches = reg_assertop.FindStringSubmatch(line)
		if len(matches) > 0 {
			op, err := dcsolver.ReadOperation(matches[1])
			if err != nil {
				log.Fatalf("line %d, %s in %s", lines, err, matches[0])
			}
			rest := matches[2]

			//   - (assert (op x n))
			mm := reg_twos.FindStringSubmatch(rest)
			if len(mm) > 0 {
				i1, found1 := names[mm[1]]
				if !found1 {
					log.Fatalf("line %d, var %s is not defined in %s", lines, mm[1], mm[0])
				}
				if i1 == 0 {
					continue
				}
				val2, err2 := strconv.Atoi(mm[2])
				if err2 != nil {
					log.Fatalf("line %d, expected constant (%s) in %s", lines, mm[2], mm[0])
				}
				if *flagv > 0 {
					fmt.Printf(";; %s %s %s\n", mm[1], matches[1], mm[2])
				}
				cg.Add(0, i1, op, val2)
				continue
			}

			//   - (assert (op (- x y) n))
			mm = reg_op1.FindStringSubmatch(rest)
			if len(mm) > 0 {
				i1, found1 := names[mm[1]]
				if !found1 {
					log.Fatalf("line %d, var %s is not defined in %s", lines, mm[1], mm[0])
				}
				i2, found2 := names[mm[2]]
				if !found2 {
					log.Fatalf("line %d, var %s is not defined in %s", lines, mm[2], mm[0])
				}
				val, err := strconv.Atoi(mm[3])
				if err != nil {
					log.Fatalf("line %d, %s is not a constant in %s", lines, mm[3], mm[0])
				}
				if *flagv > 0 {
					fmt.Printf(";; %s - %s %s %s\n", mm[1], mm[2], matches[1], mm[3])
				}
				cg.Add(i2, i1, op, val)
				continue
			}

			//   - (assert (op (- x y) (- n)))
			mm = reg_op2.FindStringSubmatch(rest)
			if len(mm) > 0 {
				i1, found1 := names[mm[1]]
				if !found1 {
					log.Fatalf("line %d, var %s is not defined in %s", lines, mm[1], mm[0])
				}
				i2, found2 := names[mm[2]]
				if !found2 {
					log.Fatalf("line %d, var %s is not defined in %s", lines, mm[2], mm[0])
				}
				val, err := strconv.Atoi(mm[3])
				if err != nil {
					log.Fatalf("line %d, %s is not a constant in %s", lines, mm[3], mm[0])
				}
				if *flagv > 0 {
					fmt.Printf(";; %s - %s %s %d\n", mm[1], mm[2], matches[1], -val)
				}
				cg.Add(i2, i1, op, -val)
				continue
			}
		}

		log.Fatalf("line %d, expression %s not recognized", lines, line)
	}

	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}

	if *flagv > 1 {
		fmt.Print(cg.PrintSMTLIB())
		fmt.Println()
	}

	if *flagv > 0 {
		fmt.Print(cg.PrintFeasible())
		fmt.Println()
	}

	if !cg.SAT {
		fmt.Print("\n*** DCSOLVE: UNSAT ***\n\n")
	} else {
		fmt.Print("\n*** DCSOLVE: SAT ***\n\n")
		fmt.Print(cg.PrintFeasible())
		fmt.Println()
	}

	callz3(cg)
}

// ********************************************************************

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
	reg_z3 := regexp.MustCompile(`\(define-fun\s+(?P<varname>[[:alpha:]][[:word:]]*)\s+\(\) Int\s*(?P<value>\d+)\s*\)`)
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
