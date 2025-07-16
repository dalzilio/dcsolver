// Copyright 2025. Silvano DAL ZILIO. All rights reserved. Use of this source
// code is governed by the MIT license that can be found in the LICENSE file.

package main

import (
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

	// We parse the input file and populate our constraint graph.
	cg, err := dcsolver.ReadSMTLIB(osfile, false)

	if err != nil {
		log.Fatalln(err)
	}

	if *flagv == 1 {
		fmt.Print(cg.PrintSystem())
		fmt.Println()
	}

	if *flagv > 1 {
		fmt.Print(cg.PrintSMTLIB())
		fmt.Println()
	}

	if !cg.SAT {
		fmt.Print("\n*** DCSOLVE: UNSAT ***\n")
	} else {
		fmt.Print("\n*** DCSOLVE: SAT ***\n")
		fmt.Print(cg.PrintFeasible())
		fmt.Println()
	}
	fmt.Println()
	issat, msg := cg.ExecZ3()
	if issat {
		fmt.Print("\n*** Z3: SAT ***\n")
		fmt.Println(msg)
		return
	}
	fmt.Print("\n*** Z3: UNSAT ***\n")
	fmt.Println(msg)
}
