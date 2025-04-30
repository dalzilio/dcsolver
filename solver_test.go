// Copyright 2025. Silvano DAL ZILIO. All rights reserved.
// Use of this source code is governed by the GPL license
// that can be found in the LICENSE file.

package dcsolver

import (
	"os"
	"path/filepath"
	"testing"
)

func TestExamples(t *testing.T) {
	filenames, err := filepath.Glob("./cmd/dcsolve/testdata/*.smt")
	if err != nil {
		t.Errorf("problem listing smt files in testdata: %s", err)
	}

	for _, tt := range filenames {
		file, err := os.Open(tt)
		if err != nil {
			t.Errorf("problem opening file %s: %s", tt, err)
		}
		defer file.Close()
		cg, err := ReadSMTLIB(file, false)
		if err != nil {
			t.Errorf("problem parsing file %s: %s", tt, err)
		}
		issat, _ := cg.ExecZ3()

		if cg.SAT != issat {
			t.Errorf("Error in file %s, z3 %v, dcs %v", tt, issat, cg.SAT)
		}
	}
}
