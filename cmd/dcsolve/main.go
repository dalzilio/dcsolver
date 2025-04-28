// Copyright 2025. Silvano DAL ZILIO. All rights reserved. Use of this source
// code is governed by the GPL license that can be found in the LICENSE file.

// Command dcsolve takes as input a file (with extension .smt) that describes a
// difference systems using a subset of smt-lib syntax, with atoms of the
// following form.
//
//   - (declare-const z Real)
//   - (assert (op (- x y) n))
//   - (assert (op (- x y) (- n)))
//   - (assert (op x n))
//   - (assert (op x (- n))
//
// where:
//   - op is one of <, <=, >, >=, or =
//   - x, y are free constant symbols of sort Real,
//   - n is a (positive) numeral.
//
// We assume that every specification starts with the line (declare-const start
// Real), where start is a reserved symbol, used to represent the start of time.
package main

import (
	"bufio"
	"fmt"
	"log"
	"os"
	"path/filepath"

	"github.com/dalzilio/dcsolver"
	flag "github.com/spf13/pflag"
)

func main() {
	var flaghelp = flag.BoolP("help", "h", false, "print this message")
	var flagv = flag.IntP("verbose", "v", 0, "textual output (use -v=2 for more info)")
	flag.Lookup("verbose").NoOptDefVal = "1"
	flag.Lookup("verbose").DefValue = "none"

	flag.CommandLine.SortFlags = false

	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "dcsolve -- Apr 2025 -- LAAS/CNRS\n")
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

	switch {
	case (N > 1):
		log.Fatal("should have exactly one smt-lib file")
	case flag.NArg() == 0:
		log.Fatal("should have exactly one smt-lib file")
	}

	var err error
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

	// We parse the input file and populate our constraint graph. We also keep a
	// association list between variables names and their index.
	cg := dcsolver.NewDCS()
	names := map[string]int{"start": 0}

	p := &parser{
		s:     &scanner{r: bufio.NewReader(osfile), pos: &textPos{}},
		depth: 0,
		ahead: false,
	}

LOOP:
	for {
		switch tok := p.scan(); tok.tok {
		case tokEOF:
			break LOOP
		case tokLPAR:
			p.depth++
		case tokRPAR:
			p.depth--
		case tokDECLARE:
			// (declare-const x Real)
			if p.depth != 1 {
				log.Fatalf("Malformed input at %s", tok.pos)
			}
			varn := p.scan()
			if varn.tok != tokVAR {
				log.Fatalf("Malformed input at %s, awaiting variable declaration, found %s", varn.pos, varn.string)
			}
			if tok := p.scan(); tok.tok != tokTYPE {
				log.Fatalf("Malformed input at %s, missing type declaration Real", tok.pos)
			}
			if err := p.scanMultiRPAR(); err != nil {
				log.Fatalf("Malformed input at %s, missing closing parenthesis", tok.pos)
			}
			if *flagv > 0 {
				fmt.Printf(";; variable \"%s\" added\n", varn.string)
			}
			if varn.string == "start" {
				continue
			}
			if _, found := names[varn.string]; found {
				log.Fatalf("variable %s redefined at %s", varn.string, varn.pos)
			}
			names[varn.string] = len(cg.Names)
			cg.AddVars(varn.string)
		case tokASSERT:
			// (assert (op ...))
			if p.depth != 1 {
				log.Fatalf("Malformed input at %s", tok.pos)
			}
			if tok := p.scan(); tok.tok != tokLPAR {
				log.Fatalf("Malformed input at %s, missing open parenthesis", tok.pos)
			}
			p.depth++
			tops := p.scan()
			if tops.tok != tokOP {
				log.Fatalf("Malformed input at %s, found %s", tops.pos, tops.string)
			}
			op := dcsolver.Operation(tops.val)
			texp := p.scan()
			switch texp.tok {
			case tokLPAR:
				// (assert (op (- y start) 2))
				p.depth++
				if tok := p.scan(); tok.tok != tokMINUS {
					log.Fatalf("Malformed input at %s, missing minus sign", tok.pos)
				}
				var1 := p.scan()
				if var1.tok != tokVAR {
					log.Fatalf("Awaiting variable at %s, found %s", var1.pos, var1.string)
				}
				var2 := p.scan()
				if var2.tok != tokVAR {
					log.Fatalf("Awaiting variable at %s, found %s", var2.pos, var2.string)
				}
				i1, found1 := names[var1.string]
				if !found1 {
					log.Fatalf("variable %s is not defined", var1.string)
				}
				i2, found2 := names[var2.string]
				if !found2 {
					log.Fatalf("variable %s is not defined", var2.string)
				}
				if err := p.scanOneRPAR(); err != nil {
					log.Fatalf("Malformed input at %s, missing closing parenthesis", tok.pos)
				}
				val, err := p.scanValue()
				if err != nil {
					log.Fatalf("Malformed input at %s, wrong value", texp.pos)
				}
				if *flagv > 0 {
					fmt.Printf(";; %s - %s %s %d\n", var1.string, var2.string, tops.string, val)
				}
				cg.Add(i2, i1, op, val)
				if !cg.SAT {
					break LOOP
				}
			case tokVAR:
				// (assert (op x 8))
				i, found := names[texp.string]
				if !found {
					log.Fatalf("variable %s is not defined", texp.string)
				}
				val, err := p.scanValue()
				if err != nil {
					log.Fatalf("Malformed input at %s, wrong value", texp.pos)
				}
				if *flagv > 0 {
					fmt.Printf(";; %s %s %d\n", texp.string, tops.string, val)
				}
				cg.Add(0, i, op, val)
				if !cg.SAT {
					break LOOP
				}
			default:
				log.Fatalf("Malformed input at %s, found %s", texp.pos, texp.string)
			}
			// parsing: ))
			if err := p.scanMultiRPAR(); err != nil {
				log.Fatalf("Malformed input at %s, missing closing parenthesis", tok.pos)
			}
		default:
			log.Fatalf("Malformed input at %s, found %s", tok.pos, tok.string)
		}
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
