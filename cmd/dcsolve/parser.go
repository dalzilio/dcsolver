// Copyright 2025. Silvano DAL ZILIO. All rights reserved.
// Use of this source code is governed by the GPL license
// that can be found in the LICENSE file.

package main

import (
	"bufio"
	"bytes"
	"fmt"
	"strconv"

	"github.com/dalzilio/dcsolver"
)

// **************************************************************************
// Tokenization
// **************************************************************************

type textPos struct {
	line   int
	column int
	ahead  int
}

func (t textPos) String() string {
	return fmt.Sprintf("{line: %d, col: %d}", t.line+1, t.column-t.ahead)
}

type tokenKind int

// tokenKind is an enumeration describing possible tokens in a net file. tokTR is
// the token for transitions 'tr' in the net format
const (
	tokMINUS   tokenKind = iota // '-'
	tokLPAR                     // '('
	tokRPAR                     // ')'
	tokVAR                      // '<varname>'
	tokOP                       // operation: '<', '=', ...
	tokDECLARE                  // 'declare-const'
	tokASSERT                   // 'assert'
	tokTYPE                     // 'Real'
	tokNUM                      // '[1-9][0-9]*'
	tokREAL                     // '[0-9]+.[0-9]+'
	tokDIVIDE                   // '/'
	tokERROR                    // malformed input
	tokEOF                      // '\0'
)

type token struct {
	tok tokenKind
	pos textPos
	string
	val int
}

var eof = rune(0)

func isDigit(ch rune) bool {
	return (ch >= '0' && ch <= '9')
}

func isIdChar(ch rune) bool {
	return (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch == '-') || isDigit(ch)
}

func isOp(ch rune) bool {
	return (ch == '<') || (ch == '>') || (ch == '=')
}

func isSpace(ch rune) bool {
	return (ch == ' ') || (ch == '\n') || (ch == '\t')
}

// **************************************************************************
// Scanner
// **************************************************************************

// scanner adds a position field for easy error reporting. We also include a
// bytes buffer that is reused between scanning methods.
type scanner struct {
	r   *bufio.Reader
	pos *textPos
	buf bytes.Buffer
}

// read reads the next rune from the bufferred reader.
// Returns the rune(0) if an error occurs (or io.EOF is returned).
func (s *scanner) read() rune {
	ch, _, err := s.r.ReadRune()
	if err != nil {
		return eof
	}
	if s.pos.ahead != 0 {
		s.pos.ahead--
	} else {
		s.pos.column++
	}
	if ch == '\n' {
		s.pos.line++
		s.pos.column = 0
	}
	return ch
}

// unread places the previously read rune back on the reader.
func (s *scanner) unread() {
	_ = s.r.UnreadRune()
	s.pos.ahead++
}

// returns a token with the current position in the file
func (s *scanner) position(t tokenKind, val int, text string) token {
	return token{tok: t, pos: *s.pos, val: val, string: text}
}

// scan returns the next token and literal value.
func (s *scanner) scan() token {
	// Read the next non whitespace rune.
	ch := s.read()
	switch {
	case ch == eof:
		return s.position(tokEOF, 0, "EOF")
	case ch == ';':
		// Start of comment, we jump to after the end of line
		for {
			ch = s.read()
			if ch == eof {
				return s.position(tokEOF, 0, "EOF")
			}
			if ch == '\n' {
				break
			}
		}
		return s.scan()
	case isSpace(ch):
		return s.scan()
	case isDigit(ch):
		return s.scanNumber(ch)
	case ch == '-':
		return s.position(tokMINUS, 0, "-")
	case isIdChar(ch):
		return s.scanId(ch)
	case isOp(ch):
		ch2 := s.read()
		if isOp(ch2) {
			res := string([]rune{ch, ch2})
			op, err := dcsolver.ReadOperation(res)
			if err != nil {
				return s.position(tokERROR, 0, err.Error())
			}
			return s.position(tokOP, int(op), res)
		}
		s.unread()
		res := string(ch)
		op, err := dcsolver.ReadOperation(res)
		if err != nil {
			return s.position(tokERROR, 0, err.Error())
		}
		return s.position(tokOP, int(op), res)
	case ch == '(':
		return s.position(tokLPAR, 0, "(")
	case ch == ')':
		return s.position(tokRPAR, 0, ")")
	default:
		return s.position(tokERROR, 0, string(ch))
	}
}

// unscan backtrack the currently  read token.
func (p *parser) unscan() {
	p.ahead = true
}

// scanNumber scan the input for digits and return the resulting number as an
// int. We accept real numbers starting with 0.
func (s *scanner) scanNumber(c rune) token {
	// Create a buffer and read the current character into it.
	isreal := false
	s.buf.Reset()
	if c != 0 {
		s.buf.WriteRune(c)
	}
	ch := s.read()
	for isDigit(ch) {
		s.buf.WriteRune(ch)
		ch = s.read()
	}
	if ch == '.' {
		isreal = true
		ch := s.read()
		for isDigit(ch) {
			s.buf.WriteRune(ch)
			ch = s.read()
		}
	}
	s.unread()
	res := s.buf.String()
	if !isreal {
		val, err := strconv.Atoi(res)
		if err != nil {
			return s.position(tokERROR, 0, err.Error())
		}
		return s.position(tokNUM, val, res)
	}
	if res[len(res)-1] == '.' {
		// The number ends with . instead of .0
		return s.position(tokERROR, 0, "malformed real value")
	}
	return s.position(tokREAL, 0, s.buf.String())
}

// scanId scan the input for valid id characters.
func (s *scanner) scanId(c rune) token {
	// Create a buffer and read the current character into it.
	s.buf.Reset()
	if c != 0 {
		s.buf.WriteRune(c)
	}
	for {
		ch := s.read()
		if !isIdChar(ch) {
			s.unread()
			break
		}
		s.buf.WriteRune(ch)
	}
	res := s.buf.String()
	switch res {
	case "declare-const":
		return s.position(tokDECLARE, 0, s.buf.String())
	case "assert":
		return s.position(tokASSERT, 0, s.buf.String())
	case "Real":
		return s.position(tokTYPE, 0, s.buf.String())
	default:
		return s.position(tokVAR, 0, s.buf.String())
	}
}

// scanValue scan the input for constant number, n, or an expression of the form
// "(- n)".
func (p *parser) scanValue() (int, error) {
	tok := p.scan()
	switch tok.tok {
	case tokNUM:
		return tok.val, nil
	case tokLPAR:
		if tok := p.scan(); tok.tok != tokMINUS {
			return 0, fmt.Errorf("malformed numerical expression")
		}
		tval := p.scan()
		if tval.tok != tokNUM {
			return 0, fmt.Errorf("malformed numerical expression")
		}
		if tok := p.scan(); tok.tok != tokRPAR {
			return 0, fmt.Errorf("malformed numerical expression")
		}
		return -tok.val, nil
	default:
		return 0, fmt.Errorf("malformed numerical expression")
	}
}

// scanMultiRPAR scan the input for successive ')' until we reach depth 0.
func (p *parser) scanMultiRPAR() error {
	for {
		if p.depth == 0 {
			return nil
		}
		if tok := p.scan(); tok.tok != tokRPAR {
			return fmt.Errorf("missing closing parenthesis")
		}
		p.depth--
		continue
	}
}

// scanOneRPAR scan the input to close one ')'.
func (p *parser) scanOneRPAR() error {
	if tok := p.scan(); tok.tok != tokRPAR {
		return fmt.Errorf("missing closing parenthesis")
	}
	p.depth--
	return nil
}

// **************************************************************************
// Parser
// **************************************************************************

// parser represents a net parser.
type parser struct {
	s     *scanner
	depth int   // number of nested parenthesis
	tok   token // last read token
	ahead bool  // true if there is a token stored in tok
}

// scan returns the next token from the underlying scanner.
// If a token has been unscanned then read that instead.
func (p *parser) scan() token {
	// If we have a token on the buffer, then return it.
	// Otherwise read the next token from the scanner.
	// and save it to the buffer in case we unscan later.
	if p.ahead {
		p.ahead = false
	} else {
		p.tok = p.s.scan()
	}
	return p.tok
}
