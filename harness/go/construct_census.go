// construct_census.go — the Go tier's construct census instrument.
//
// Mirrors harness/c_construct_census.py: it walks a corpus with the
// language's OWN front end (go/parser + go/ast, the same packages the
// compiler's type checker is built beside), counts every construct it
// finds, and emits sorted, deterministic JSON. A double run is
// byte-identical.
//
// Usage — BUILD IT, do not `go run` it:
//
//	go build -o <bin> harness/go/construct_census.go
//	<bin> --root <dir> <path>... -o docs/go-construct-census.json
//	<bin> --root <dir> <path>... --compare docs/go-construct-census.json
//
// A <path> is a .go file or a directory (walked recursively; testdata/,
// vendor/ and dot-directories are skipped). Use harness/go/census.sh,
// which does the build for you.
//
// TWO `go run` TRAPS, both measured, and together they are why the
// documented invocation is a build:
//
//  1. `go run` does NOT propagate the program's exit code. A program
//     that exits 3 makes `go run` print "exit status 3" and exit 1.
//     This instrument's whole refusal taxonomy is carried in its exit
//     code, so under `go run` every distinct cause collapses to 1 and
//     the "3 and 4 are never agreement" invariant is destroyed silently.
//  2. `go run a.go b.go` treats BOTH as SOURCES of one package. Since
//     this instrument's arguments are themselves .go paths, the
//     invocation is ambiguous unless a non-.go flag comes first.
//
// THE THREE REFUSAL PATHS, all of which exit non-zero and say why:
//
//	2  a path does not exist, or no .go file was found under it
//	3  a file does not PARSE — go/parser, like clang, returns a partial
//	   tree alongside its error, and a census of a partial tree is a
//	   plausible-looking wrong answer. We refuse instead.
//	4  the census attributed ZERO nodes — an empty census is an
//	   instrument fault, never a finding. NOTE: this guard is
//	   UNREACHABLE as the instrument stands, because ast.Inspect over a
//	   successfully parsed file always visits at least the File and its
//	   package Ident. It is kept because the thing that made the same
//	   guard fire in the C instrument was a source FILTER (clang's
//	   sticky loc.file, without which the census measured libc's
//	   headers). Add any comparable filter here and it goes live.
//	5  --compare found a difference (the difference is printed).
//
// The toolchain FAMILY is stamped, never the point release. The
// language version is stamped separately and per file, because in Go
// the language version is an INPUT to the semantics, not a label on the
// side of it: `for` loop variable scoping differs between a file
// declared go1.21 and one declared go1.22 under the SAME compiler.
package main

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"reflect"
	"runtime"
	"sort"
	"strings"
)

const schemaVersion = "go-census-0.1"

// Census is the whole output document. Every map is emitted by
// encoding/json, which sorts map keys, so the output is deterministic
// without any further care.
type Census struct {
	Schema          string            `json:"schema"`
	ToolchainFamily string            `json:"toolchain_family"`
	LangVersions    map[string]int    `json:"lang_versions"`
	Files           int               `json:"files"`
	SourceSHA       map[string]string `json:"source_sha256"`
	LinesTotal      int               `json:"lines_total"`
	LinesNonBlank   int               `json:"lines_non_blank"`
	Bytes           int               `json:"bytes"`
	Nodes           int               `json:"nodes"`
	NodeKinds       map[string]int    `json:"node_kinds"`
	NodeKindCount   int               `json:"node_kind_count"`
	Decls           map[string]int    `json:"decls"`
	BinaryOps       map[string]int    `json:"binary_ops"`
	UnaryOps        map[string]int    `json:"unary_ops"`
	AssignOps       map[string]int    `json:"assign_ops"`
	IncDecOps       map[string]int    `json:"incdec_ops"`
	BranchOps       map[string]int    `json:"branch_ops"`
	Concurrency     map[string]int    `json:"concurrency"`
	ChanDirs        map[string]int    `json:"chan_dirs"`
	RangeOver       map[string]int    `json:"range_over"`
	Builtins        map[string]int    `json:"builtin_calls"`
	Imports         map[string]int    `json:"imports"`
	ImportsExternal []string          `json:"imports_external"`
	Literals        map[string]int    `json:"basic_lit_kinds"`
	// Shapes: sub-forms of a construct that a NODE COUNT cannot see.
	// `SwitchStmt: 5186` says nothing about how many carry a
	// `fallthrough` (208) or an init clause (258), and those are what
	// decide what a rule costs. Added for rung 2's scoping.
	Shapes map[string]int `json:"shapes"`

	// root is not emitted: it only decides how source paths are
	// SPELLED in the output, so that a census taken under one
	// checkout compares against one taken under another.
	root string
}

// name spells a censused path relative to --root, so the output does
// not embed the absolute location of a toolchain or a clone. The
// corpus is cross-repo by construction, and a path relative to this
// repository's root would be a fiction.
func (c *Census) name(path string) string {
	if c.root != "" {
		if rel, err := filepath.Rel(c.root, path); err == nil && !strings.HasPrefix(rel, "..") {
			return filepath.ToSlash(rel)
		}
	}
	return filepath.ToSlash(path)
}

func newCensus() *Census {
	return &Census{
		Schema:          schemaVersion,
		ToolchainFamily: toolchainFamily(),
		LangVersions:    map[string]int{},
		SourceSHA:       map[string]string{},
		NodeKinds:       map[string]int{},
		Decls:           map[string]int{},
		BinaryOps:       map[string]int{},
		UnaryOps:        map[string]int{},
		AssignOps:       map[string]int{},
		IncDecOps:       map[string]int{},
		BranchOps:       map[string]int{},
		Concurrency:     map[string]int{},
		ChanDirs:        map[string]int{},
		RangeOver:       map[string]int{},
		Builtins:        map[string]int{},
		Imports:         map[string]int{},
		Literals:        map[string]int{},
		Shapes:          map[string]int{},
	}
}

// toolchainFamily reports go1.N, never the point release — the same
// rule harness/c_construct_census.py applies to clang. A census that
// changed because a patch release shipped would be noise.
func toolchainFamily() string {
	v := runtime.Version() // e.g. "go1.25.6"
	parts := strings.SplitN(strings.TrimPrefix(v, "go"), ".", 3)
	if len(parts) >= 2 {
		return "go" + parts[0] + "." + parts[1]
	}
	return v
}

// goBuildVersion reads a //go:build go1.N constraint if the file
// carries one. Go selects per-file language semantics from the module's
// `go` directive, overridden by such a line; the census records what it
// can SEE, and says so rather than guessing the module's.
func goBuildVersion(src []byte) string {
	for _, line := range strings.Split(string(src), "\n") {
		line = strings.TrimSpace(line)
		if line == "" || strings.HasPrefix(line, "//") {
			if strings.HasPrefix(line, "//go:build ") {
				for _, tok := range strings.Fields(strings.TrimPrefix(line, "//go:build ")) {
					if strings.HasPrefix(tok, "go1.") {
						return tok
					}
				}
			}
			continue
		}
		if strings.HasPrefix(line, "package ") {
			break
		}
	}
	return "(from go.mod)"
}

// The predeclared TYPE names. A call whose callee is one of these is a
// conversion, not a call — see the CallExpr arm.
var builtinTypeNames = map[string]bool{
	"bool": true, "byte": true, "complex64": true, "complex128": true,
	"error": true, "float32": true, "float64": true, "int": true,
	"int8": true, "int16": true, "int32": true, "int64": true, "rune": true,
	"string": true, "uint": true, "uint8": true, "uint16": true,
	"uint32": true, "uint64": true, "uintptr": true, "any": true,
}

var builtinNames = map[string]bool{
	"append": true, "cap": true, "clear": true, "close": true, "complex": true,
	"copy": true, "delete": true, "imag": true, "len": true, "make": true,
	"max": true, "min": true, "new": true, "panic": true, "print": true,
	"println": true, "real": true, "recover": true,
}

func main() {
	var paths []string
	var out, compare, root, ladder, kindsets string
	var reach, resolve bool
	args := os.Args[1:]
	for i := 0; i < len(args); i++ {
		switch args[i] {
		case "--root":
			i++
			if i >= len(args) {
				die(2, "--root needs a path")
			}
			root = args[i]
		case "-o", "--out":
			i++
			if i >= len(args) {
				die(2, "-o needs a path")
			}
			out = args[i]
		case "--compare":
			i++
			if i >= len(args) {
				die(2, "--compare needs a path")
			}
			compare = args[i]
		case "--kindsets":
			i++
			if i >= len(args) {
				die(2, "--kindsets needs an output path")
			}
			kindsets = args[i]
		case "--reach":
			reach = true
		case "--resolve":
			resolve = true
		case "--ladder":
			i++
			if i >= len(args) {
				die(2, "--ladder needs a baseline census JSON")
			}
			ladder = args[i]
		default:
			paths = append(paths, args[i])
		}
	}
	if resolve {
		runResolveSelfTest()
		return
	}
	if reach {
		runReach(paths, root)
		return
	}
	if len(paths) == 0 {
		die(2, "usage: construct_census.go <path>... [-o out.json] [--compare ref.json] [--ladder base.json]")
	}

	files, err := collect(paths)
	if err != nil {
		die(2, err.Error())
	}
	if len(files) == 0 {
		die(2, fmt.Sprintf("no .go files found under %v", paths))
	}

	if kindsets != "" {
		runKindSets(files, kindsets, root)
		return
	}
	if ladder != "" {
		runLadder(files, ladder)
		return
	}

	c := newCensus()
	c.root = root
	for _, f := range files {
		if err := c.censusFile(f); err != nil {
			// A partial tree is a wrong answer wearing a plausible
			// face. Refuse, and name the file.
			die(3, fmt.Sprintf("%s does not parse: %v", f, err))
		}
	}
	if c.Nodes == 0 {
		die(4, fmt.Sprintf("censused %d file(s) and attributed ZERO nodes — instrument fault, not a finding", len(files)))
	}
	c.NodeKindCount = len(c.NodeKinds)
	sort.Strings(c.ImportsExternal)

	blob, err := json.MarshalIndent(c, "", "  ")
	if err != nil {
		die(1, err.Error())
	}
	blob = append(blob, '\n')

	if compare != "" {
		ref, err := os.ReadFile(compare)
		if err != nil {
			die(2, fmt.Sprintf("cannot read %s: %v", compare, err))
		}
		if string(ref) == string(blob) {
			fmt.Fprintf(os.Stderr, "census matches %s\n", compare)
			return
		}
		die(5, diff(ref, blob))
	}
	if out != "" {
		if err := os.WriteFile(out, blob, 0o644); err != nil {
			die(1, err.Error())
		}
		fmt.Fprintf(os.Stderr, "wrote %s (%d files, %d nodes, %d kinds)\n", out, c.Files, c.Nodes, c.NodeKindCount)
		return
	}
	os.Stdout.Write(blob)
}

// diff reports the differing top-level keys, with the scalar deltas
// spelled out, so a --compare failure is actionable without a
// second tool.
func diff(refBlob, gotBlob []byte) string {
	var ref, got map[string]any
	if json.Unmarshal(refBlob, &ref) != nil || json.Unmarshal(gotBlob, &got) != nil {
		return "census differs from the reference (and one of them is not JSON)"
	}
	keys := map[string]bool{}
	for k := range ref {
		keys[k] = true
	}
	for k := range got {
		keys[k] = true
	}
	var names []string
	for k := range keys {
		names = append(names, k)
	}
	sort.Strings(names)
	var b strings.Builder
	b.WriteString("census DIFFERS from the reference:\n")
	for _, k := range names {
		a, _ := json.Marshal(ref[k])
		c, _ := json.Marshal(got[k])
		if string(a) == string(c) {
			continue
		}
		if len(a) > 200 {
			a = append(a[:200], "..."...)
		}
		if len(c) > 200 {
			c = append(c[:200], "..."...)
		}
		fmt.Fprintf(&b, "  %-20s ref=%s\n  %-20s got=%s\n", k, a, "", c)
	}
	return b.String()
}

func collect(paths []string) ([]string, error) {
	var files []string
	for _, p := range paths {
		st, err := os.Stat(p)
		if err != nil {
			return nil, err
		}
		if !st.IsDir() {
			files = append(files, p)
			continue
		}
		err = filepath.WalkDir(p, func(path string, d os.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if d.IsDir() {
				n := d.Name()
				if n != "." && (strings.HasPrefix(n, ".") || n == "vendor" || n == "testdata") {
					return filepath.SkipDir
				}
				return nil
			}
			if strings.HasSuffix(path, ".go") {
				files = append(files, path)
			}
			return nil
		})
		if err != nil {
			return nil, err
		}
	}
	sort.Strings(files)
	return files, nil
}

func (c *Census) censusFile(path string) error {
	src, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, path, src, parser.ParseComments|parser.SkipObjectResolution)
	if err != nil {
		return err
	}

	c.Files++
	c.Bytes += len(src)
	c.SourceSHA[c.name(path)] = sha256hex(src)
	c.LangVersions[goBuildVersion(src)]++
	// Strip ONE trailing newline before splitting. A file ending in
	// "\n" splits into a final empty segment that is not a line, and
	// counting it would report 111 for a 110-line file — a small
	// wrong number, which is still a wrong number.
	text := strings.TrimSuffix(string(src), "\n")
	if text != "" {
		for _, line := range strings.Split(text, "\n") {
			c.LinesTotal++
			if strings.TrimSpace(line) != "" {
				c.LinesNonBlank++
			}
		}
	}

	for _, imp := range f.Imports {
		p := strings.Trim(imp.Path.Value, `"`)
		c.Imports[p]++
		// An import path whose first segment contains a dot is a
		// module path, not a standard-library package. That is the
		// language's own rule, not a heuristic.
		if first, _, _ := strings.Cut(p, "/"); strings.Contains(first, ".") {
			if !contains(c.ImportsExternal, p) {
				c.ImportsExternal = append(c.ImportsExternal, p)
			}
		}
	}

	ast.Inspect(f, func(n ast.Node) bool {
		if n == nil {
			return true
		}
		c.Nodes++
		c.NodeKinds[kindOf(n)]++

		switch x := n.(type) {
		case *ast.FuncDecl:
			if x.Recv != nil {
				c.Decls["method"]++
				c.Shapes["funcdecl_method"]++
			} else {
				c.Decls["func"]++
				c.Shapes["funcdecl_plain"]++
			}
			if x.Body == nil {
				c.Decls["func_no_body"]++
			}
			nres := 0
			if x.Type.Results != nil {
				for _, fl := range x.Type.Results.List {
					if n := len(fl.Names); n > 0 {
						nres += n
					} else {
						nres++
					}
				}
			}
			c.Shapes[fmt.Sprintf("funcdecl_%d_results", nres)]++
			npar := 0
			variadic := false
			if x.Type.Params != nil {
				for _, fl := range x.Type.Params.List {
					if n := len(fl.Names); n > 0 {
						npar += n
					} else {
						npar++
					}
					if _, isEll := fl.Type.(*ast.Ellipsis); isEll {
						variadic = true
					}
				}
			}
			c.Shapes[fmt.Sprintf("funcdecl_%d_params", npar)]++
			if variadic {
				c.Shapes["funcdecl_variadic"]++
			}
			if x.Type.TypeParams != nil {
				c.Shapes["funcdecl_generic"]++
			}
		case *ast.GenDecl:
			c.Decls[x.Tok.String()]++
		case *ast.BinaryExpr:
			c.BinaryOps[x.Op.String()]++
		case *ast.UnaryExpr:
			c.UnaryOps[x.Op.String()]++
			if x.Op == token.ARROW {
				c.Concurrency["receive_expr"]++
			}
		case *ast.AssignStmt:
			c.AssignOps[x.Tok.String()]++
		case *ast.IncDecStmt:
			c.IncDecOps[x.Tok.String()]++
		case *ast.BranchStmt:
			c.BranchOps[x.Tok.String()]++
			if x.Label != nil {
				c.Shapes["branch_labeled_"+x.Tok.String()]++
			}
		case *ast.BasicLit:
			c.Literals[x.Kind.String()]++
		case *ast.GoStmt:
			c.Concurrency["go_stmt"]++
		case *ast.SendStmt:
			c.Concurrency["send_stmt"]++
		case *ast.SelectStmt:
			c.Concurrency["select_stmt"]++
			n := 0
			hasDefault := false
			for _, cl := range x.Body.List {
				if cc, ok := cl.(*ast.CommClause); ok {
					n++
					if cc.Comm == nil {
						hasDefault = true
					}
				}
			}
			c.Concurrency[fmt.Sprintf("select_with_%d_cases", n)]++
			if hasDefault {
				c.Concurrency["select_with_default"]++
			}
		case *ast.CommClause:
			c.Concurrency["comm_clause"]++
		case *ast.ChanType:
			c.Concurrency["chan_type"]++
			switch {
			case x.Dir == ast.SEND|ast.RECV:
				c.ChanDirs["bidirectional"]++
			case x.Dir == ast.SEND:
				c.ChanDirs["send_only"]++
			case x.Dir == ast.RECV:
				c.ChanDirs["recv_only"]++
			}
		case *ast.DeferStmt:
			c.Concurrency["defer_stmt"]++
		case *ast.RangeStmt:
			// What a range ranges OVER is a type question the census
			// cannot answer without go/types; what it CAN answer is
			// the syntactic shape, which is what it reports.
			switch x.X.(type) {
			case *ast.CallExpr:
				c.RangeOver["call_result"]++
			case *ast.Ident:
				c.RangeOver["ident"]++
			case *ast.SelectorExpr:
				c.RangeOver["selector"]++
			default:
				c.RangeOver["other"]++
			}
			c.Shapes["range_total"]++
			if x.Tok == token.DEFINE {
				c.RangeOver["declares_vars"]++
				c.Shapes["range_declares_vars"]++
			}
			if x.Key != nil && x.Value != nil {
				c.Shapes["range_two_vars"]++
			}
		case *ast.ForStmt:
			c.Shapes["for_total"]++
			if x.Init == nil && x.Cond == nil && x.Post == nil {
				// `for {}` — the most common for-loop form, and the one
				// where fuel is load-bearing rather than a formality.
				c.Shapes["for_bare"]++
			}
			if a, ok := x.Init.(*ast.AssignStmt); ok && a.Tok == token.DEFINE {
				// The loop form whose scoping CHANGED at go1.22.
				c.RangeOver["for_clause_declares_vars"]++
				c.Shapes["for_declares_vars"]++
				if len(a.Lhs) > 1 {
					c.Shapes["for_declares_multi"]++
				}
			}
		case *ast.SwitchStmt:
			c.Shapes["switch_total"]++
			if x.Tag == nil {
				c.Shapes["switch_tagless"]++
			} else {
				c.Shapes["switch_tagged"]++
			}
			if x.Init != nil {
				c.Shapes["switch_with_init"]++
			}
			nc := 0
			for _, st := range x.Body.List {
				if cc, ok := st.(*ast.CaseClause); ok {
					nc++
					if cc.List == nil {
						c.Shapes["switch_with_default"]++
					} else if len(cc.List) == 1 {
						c.Shapes["case_single_expr"]++
					} else {
						c.Shapes["case_multi_expr"]++
					}
				}
			}
			c.Shapes[fmt.Sprintf("switch_with_%d_cases", nc)]++
		case *ast.TypeSwitchStmt:
			c.Shapes["typeswitch_total"]++
			if x.Init != nil {
				c.Shapes["typeswitch_with_init"]++
			}
		case *ast.TypeSpec:
			c.Shapes["typespec_total"]++
			if x.Assign.IsValid() {
				c.Shapes["typespec_alias"]++
			}
			if x.TypeParams != nil {
				c.Shapes["typespec_generic"]++
			}
			switch x.Type.(type) {
			case *ast.StructType:
				c.Shapes["typespec_struct"]++
			case *ast.InterfaceType:
				c.Shapes["typespec_interface"]++
			default:
				c.Shapes["typespec_other"]++
			}
		case *ast.ArrayType:
			// `[N]T` and `[]T` are the SAME node kind; only `Len` tells
			// them apart, and they are different semantic objects — a
			// fixed array is a value, a slice is a header. Counting the
			// kind alone cannot size the rung.
			if x.Len == nil {
				c.Shapes["arraytype_slice"]++
			} else {
				c.Shapes["arraytype_fixed"]++
			}
		case *ast.CallExpr:
			c.Shapes["call_total"]++
			// A CONVERSION `int(e)` parses as a CallExpr on an Ident, and
			// is indistinguishable from a call to a function named `int`
			// without go/types. The builtin type names are the one case a
			// syntactic census CAN separate, and the rung needs them.
			if id, ok := x.Fun.(*ast.Ident); ok && builtinTypeNames[id.Name] {
				c.Shapes["call_builtin_type_conversion"]++
			}
			switch fn := x.Fun.(type) {
			case *ast.Ident:
				if builtinNames[fn.Name] {
					c.Builtins[fn.Name]++
					c.Shapes["call_builtin"]++
				} else {
					// The shape this tier models: a call to a plain name.
					c.Shapes["call_plain_ident"]++
				}
			case *ast.SelectorExpr:
				// `pkg.F(...)` or `x.M(...)` — indistinguishable without
				// go/types, which is exactly why they are one bucket.
				c.Shapes["call_selector"]++
			default:
				c.Shapes["call_other"]++
			}
			if x.Ellipsis.IsValid() {
				c.Shapes["call_variadic_spread"]++
			}
		}
		return true
	})
	return nil
}

// kindOf is the node's Go type name with the package qualifier and
// pointer stripped — "GoStmt", not "*ast.GoStmt". go/ast's vocabulary
// IS its set of types, so reflection is the faithful reading of it and
// a hand-written switch would be a second list to keep in sync.
func kindOf(n ast.Node) string {
	t := reflect.TypeOf(n)
	for t.Kind() == reflect.Ptr {
		t = t.Elem()
	}
	return t.Name()
}

func sha256hex(b []byte) string {
	s := sha256.Sum256(b)
	return hex.EncodeToString(s[:])
}

func contains(xs []string, s string) bool {
	for _, x := range xs {
		if x == s {
			return true
		}
	}
	return false
}

func die(code int, msg string) {
	fmt.Fprintf(os.Stderr, "construct_census: %s\n", msg)
	os.Exit(code)
}

// ---------------------------------------------------------------- ladder
//
// THE REACH LADDER.  Which node kinds unlock the most real code?
//
// The census aggregates kinds across a corpus, which answers "what is in
// there" but NOT "what would I have to build next".  A file is reachable
// only when EVERY kind it uses is modelled, so reach is a property of a
// file's whole kind SET, and adding a kind unlocks a file only when it was
// that file's LAST missing one.  This mode computes the greedy ladder: at
// each step add the single kind that unblocks the most still-blocked files.
//
// It mirrors docs/c23-goal.md §4, which computed the same curve for C and
// found the decision-relevant result there too — the ladder above the
// baseline is SHORT.  The baseline is read from a census JSON so the rung-0
// driver's own vocabulary is the starting point rather than a guess.

type ladderStep struct {
	Kind          string `json:"kind"`
	NewlyCovered  int    `json:"newly_covered"`
	CumulativeHit int    `json:"cumulative_covered"`
	FilesUsing    int    `json:"files_using_kind"`
}

func runLadder(files []string, baselinePath string) {
	blob, err := os.ReadFile(baselinePath)
	if err != nil {
		die(2, fmt.Sprintf("cannot read baseline %s: %v", baselinePath, err))
	}
	var base struct {
		NodeKinds map[string]int `json:"node_kinds"`
	}
	if err := json.Unmarshal(blob, &base); err != nil {
		die(2, fmt.Sprintf("baseline %s is not a census JSON: %v", baselinePath, err))
	}
	if len(base.NodeKinds) == 0 {
		die(4, "baseline census lists ZERO node kinds — that is an instrument fault, not a finding")
	}
	have := map[string]bool{}
	for k := range base.NodeKinds {
		have[k] = true
	}

	// Per-file kind sets. A file that does not parse is SKIPPED and
	// counted, never silently treated as an empty (and therefore
	// trivially reachable) file — that would flatter every number below.
	var sets []map[string]bool
	unparsed := 0
	for _, f := range files {
		ks, err := fileKindSet(f)
		if err != nil {
			unparsed++
			continue
		}
		sets = append(sets, ks)
	}
	if len(sets) == 0 {
		die(4, "no file yielded a kind set")
	}

	blocked := func(known map[string]bool) (covered int, missing map[string]int) {
		missing = map[string]int{}
		for _, ks := range sets {
			var miss []string
			for k := range ks {
				if !known[k] {
					miss = append(miss, k)
				}
			}
			if len(miss) == 0 {
				covered++
				continue
			}
			// Only a file's LAST missing kind can be unlocked by one
			// addition, so a file with two or more gaps votes for none.
			if len(miss) == 1 {
				missing[miss[0]]++
			}
		}
		return
	}

	usage := map[string]int{}
	for _, ks := range sets {
		for k := range ks {
			usage[k]++
		}
	}

	known := map[string]bool{}
	for k := range have {
		known[k] = true
	}
	cov0, _ := blocked(known)

	var steps []ladderStep
	for {
		_, miss := blocked(known)
		best, bestN := "", 0
		for k, n := range miss {
			if n > bestN || (n == bestN && k < best) {
				best, bestN = k, n
			}
		}
		if best == "" || bestN == 0 {
			break
		}
		known[best] = true
		cov, _ := blocked(known)
		steps = append(steps, ladderStep{best, bestN, cov, usage[best]})
	}

	out := struct {
		Schema        string       `json:"schema"`
		Baseline      string       `json:"baseline"`
		BaselineKinds int          `json:"baseline_kind_count"`
		Files         int          `json:"files"`
		Unparsed      int          `json:"files_unparsed_skipped"`
		BaselineCover int          `json:"baseline_files_covered"`
		Steps         []ladderStep `json:"ladder"`
	}{"go-ladder-0.1", filepath.ToSlash(baselinePath), len(have), len(sets), unparsed, cov0, steps}

	b, _ := json.MarshalIndent(out, "", "  ")
	os.Stdout.Write(append(b, '\n'))
}

func fileKindSet(path string) (map[string]bool, error) {
	src, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, path, src, parser.ParseComments|parser.SkipObjectResolution)
	if err != nil {
		return nil, err
	}
	ks := map[string]bool{}
	ast.Inspect(f, func(n ast.Node) bool {
		if n != nil {
			ks[kindOf(n)] = true
		}
		return true
	})
	return ks, nil
}

// runKindSets dumps one line per file: "<path>\t<kind>,<kind>,...".
// The ladder answers one question; this lets any candidate scope be
// SCORED without re-parsing 5,419 files, which is what makes a rung's
// boundary a measurement rather than a preference.
func runKindSets(files []string, outPath, root string) {
	c := &Census{root: root}
	var b strings.Builder
	skipped := 0
	for _, f := range files {
		ks, err := fileKindSet(f)
		if err != nil {
			skipped++
			continue
		}
		names := make([]string, 0, len(ks))
		for k := range ks {
			names = append(names, k)
		}
		sort.Strings(names)
		fmt.Fprintf(&b, "%s\t%s\n", c.name(f), strings.Join(names, ","))
	}
	if err := os.WriteFile(outPath, []byte(b.String()), 0o644); err != nil {
		die(1, err.Error())
	}
	fmt.Fprintf(os.Stderr, "wrote %s (%d files, %d unparsed skipped)\n", outPath, len(files)-skipped, skipped)
}


// ---------------------------------------------------------------------------
// --reach : WHICH FILES THE WALKER COULD STEP ENTIRELY
//
// docs/backlog/go.md §G16 published a reach table (baseline 1,289 files;
// the slice family taking it to 2,308) that was computed AD HOC and left
// no instrument behind, so its numbers could not be re-derived from the
// repository. This mode is that instrument. It exists because §G19 had to
// re-measure the family's promise and found nothing to re-run.
//
// TWO THINGS THIS DOES THAT A KIND-SET TSV CANNOT
//
//  1. It SPLITS `ArrayType`. go/ast spells `[]T` and `[N]T` with the same
//     node, distinguished only by `Len == nil`. The walker models slices
//     and NOT fixed arrays (the vocabulary law: declare only what the rung
//     executes), so a census that cannot tell them apart cannot state this
//     tier's reach at all. Emitted as `ArrayType/slice` / `ArrayType/fixed`.
//
//  2. It keeps the vocabulary as DATA in one place, versioned below, so a
//     rung that widens the walker widens this list in the same commit and
//     the number moves for a reason a reader can see.
//
// GO_REACH_ADD=Kind1,Kind2 widens the baseline vocabulary for one run. It
// is how §G19 established that §G16's unreproducible figures had counted
// `SelectorExpr` as steppable (baseline 512 -> 1,114, against §G16's 1,289)
// though §G8 ruled selector resolution `go/types` work that this walker
// refuses. Use it to ASK what a vocabulary would buy; never to publish a
// number the walker cannot actually step.
//
// The vocabulary is the walker's, transcribed from LeanModels/Go/Stmt.lean.
// A file is REACHABLE when every kind it uses is in the set — the
// conjunctive coverage law (§G1): bundles do not compose additively, so
// membership is `⊆`, never a score.
// ---------------------------------------------------------------------------

// walkerVocab is the set of go/ast kinds LeanModels/Go/Stmt.lean steps.
// Keep in step with the Expr/Stmt constructors; §G19 is its baseline.
var walkerVocab = []string{
	// file structure and declarations
	"File", "Comment", "CommentGroup", "FuncDecl", "FuncType", "Field",
	"FieldList", "GenDecl", "ImportSpec", "ValueSpec", "TypeSpec", "DeclStmt",
	// expressions
	"Ident", "BasicLit", "ParenExpr", "BinaryExpr", "UnaryExpr", "StarExpr",
	"CallExpr", "IndexExpr", "StructType", "CompositeLit", "KeyValueExpr",
	// statements
	"BlockStmt", "AssignStmt", "ExprStmt", "IfStmt", "ForStmt", "ReturnStmt",
	"IncDecStmt", "BranchStmt", "LabeledStmt", "EmptyStmt",
	// the slice family (§G17–§G19) and fixed arrays (§G20)
	"SliceExpr", "RangeStmt", "ArrayType/slice", "ArrayType/fixed",
}

// frontier is what the walker does NOT step, ranked by this instrument.
// §G19's retraction of the +0 law applies to every row: a delta here is a
// property of the CURRENT vocabulary and is not a ranking for any future
// one, so re-run rather than quoting an old row.
var frontier = []string{
	"SelectorExpr/pkg", "SelectorExpr/value", "SwitchStmt", "CaseClause", "FuncLit", "MapType",
	"InterfaceType", "TypeAssertExpr", "TypeSwitchStmt", "DeferStmt",
	"GoStmt", "ChanType", "SendStmt", "SelectStmt", "CommClause", "Ellipsis",
}

// importNames returns the identifiers this file binds to imported
// packages — the alias when there is one, else the path's last segment.
//
// The last segment is a HEURISTIC and the census says so: a package whose
// name differs from its directory (`gopkg.in/yaml.v2` -> `yaml`) is missed.
// It is sound in the direction that matters here — a missed import makes a
// selector look like a VALUE selector, i.e. it under-counts the rung that
// is cheap and over-counts the rung that is expensive.
func importNames(f *ast.File) map[string]bool {
	m := map[string]bool{}
	for _, im := range f.Imports {
		if im.Name != nil {
			if im.Name.Name != "_" && im.Name.Name != "." {
				m[im.Name.Name] = true
			}
			continue
		}
		p := strings.Trim(im.Path.Value, `"`)
		if i := strings.LastIndex(p, "/"); i >= 0 {
			p = p[i+1:]
		}
		if i := strings.Index(p, "."); i > 0 { // gopkg.in/yaml.v2 -> yaml
			p = p[:i]
		}
		m[p] = true
	}
	return m
}

// fileKinds returns the kind set of one file, with ArrayType and
// SelectorExpr SPLIT.
//
// Both splits exist for the same reason: go/ast spells two things this
// tier prices differently with ONE node, so a census that cannot separate
// them cannot state the tier's reach.
//
//   - ArrayType: `[]T` (modelled, §G18) vs `[N]T` (modelled, §G20).
//   - SelectorExpr: `pkg.F`, resolvable SYNTACTICALLY from the file's own
//     import list, vs `x.field` / `x.Method()`, which need go/types. This
//     is the split that prices the extractor tier's rungs (§G21), and
//     §G20 measured the undivided node at +1,189 — 23x the next
//     construct — which is what authorized that tier.
func fileKinds(path string) (map[string]bool, bool) {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, path, nil, parser.SkipObjectResolution)
	if err != nil {
		return nil, false
	}
	imports := importNames(f)
	ks := map[string]bool{}
	ast.Inspect(f, func(n ast.Node) bool {
		if n == nil {
			return true
		}
		switch x := n.(type) {
		case *ast.ArrayType:
			if x.Len == nil {
				ks["ArrayType/slice"] = true
			} else {
				ks["ArrayType/fixed"] = true
			}
			return true
		case *ast.SelectorExpr:
			if id, ok := x.X.(*ast.Ident); ok && imports[id.Name] {
				ks["SelectorExpr/pkg"] = true
			} else {
				ks["SelectorExpr/value"] = true
			}
			return true
		}
		name := strings.TrimPrefix(fmt.Sprintf("%T", n), "*ast.")
		ks[name] = true
		return true
	})
	return ks, true
}

func covered(ks map[string]bool, vocab map[string]bool) bool {
	for k := range ks {
		if !vocab[k] {
			return false
		}
	}
	return true
}

func setOf(xs ...[]string) map[string]bool {
	m := map[string]bool{}
	for _, g := range xs {
		for _, x := range g {
			m[x] = true
		}
	}
	return m
}

func runReach(paths []string, root string) {
	if root == "" && len(paths) > 0 {
		root = paths[0]
	}
	if len(paths) == 0 {
		die(2, "--reach needs a path")
	}
	var all []map[string]bool
	for _, p := range paths {
		filepath.WalkDir(p, func(q string, d os.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if d.IsDir() {
				n := d.Name()
				if strings.HasPrefix(n, ".") || n == "testdata" || n == "vendor" {
					return filepath.SkipDir
				}
				return nil
			}
			if !strings.HasSuffix(q, ".go") || strings.HasSuffix(q, "_test.go") {
				return nil
			}
			if ks, ok := fileKinds(q); ok {
				all = append(all, ks)
			}
			return nil
		})
	}
	count := func(vocab map[string]bool) int {
		n := 0
		for _, ks := range all {
			if covered(ks, vocab) {
				n++
			}
		}
		return n
	}
	extra := []string{}
	if e := os.Getenv("GO_REACH_ADD"); e != "" {
		extra = strings.Split(e, ",")
		fmt.Printf("(vocabulary widened by GO_REACH_ADD=%s)\n", e)
	}
	walkerVocab = append(walkerVocab, extra...)
	base := setOf(walkerVocab)
	b := count(base)
	fmt.Printf("go-reach-0.1  toolchain %s\n", toolchainFamily())
	fmt.Printf("files parsed (non-test): %d\n\n", len(all))
	fmt.Printf("%-34s %6d\n", "BASELINE walker vocabulary", b)
	fmt.Printf("%-34s %6s %8s\n", "", "files", "delta")
	type row struct {
		k string
		n int
	}
	var rows []row
	for _, k := range frontier {
		rows = append(rows, row{k, count(setOf(walkerVocab, []string{k}))})
	}
	sort.Slice(rows, func(i, j int) bool { return rows[i].n > rows[j].n })
	fmt.Println("\nTHE FRONTIER — what each unmodelled construct would add ALONE.")
	fmt.Println("(§G19: a delta is a property of THIS vocabulary, never a ranking")
	fmt.Println(" for a future one — RangeStmt measured +0 alone and was worth +9")
	fmt.Println(" inside the family it shipped in.)")
	for _, r := range rows {
		fmt.Printf("  + %-30s %6d %+8d\n", r.k, r.n, r.n-b)
	}
	whole := count(setOf(walkerVocab, frontier))
	fmt.Printf("  %-32s %6d %+8d\n", "+ ALL of the frontier", whole, whole-b)
}

// ---------------------------------------------------------------------------
// --resolve : THE E1 RESOLVER, and the shadowing gate it owes
//
// Rung E1 (docs/backlog/go.md §G21) resolves `pkg.F(...)` to a
// (package-path, function) pair from the FILE'S OWN IMPORT TABLE — no
// go/types. The walker then dispatches on `Expr.callPkg`.
//
// THE DISCIPLINE THIS MODE EXISTS FOR
//
// A resolution can be WRONG, not merely missing, and that is a refusal
// shape the tier had not met before: every earlier refusal was an absence.
// `bits` can be a local variable shadowing the import, and the census found
// **484 such binding sites across 198 standard-library files** — including
// `local "hash" shadows import "hash"` and `local "crc32" shadows import
// "hash/crc32"`. A resolver that ignores scope reports those as package
// calls and the walker executes the wrong function silently.
//
// The gate is TWO-SIDED, because both failure directions are real:
//
//   - resolve a SHADOWED use  -> a wrong answer (the dangerous direction);
//   - refuse an unshadowed use -> lost reach (the timid direction, which a
//     naive "is this name bound anywhere in the function?" check causes,
//     since Go's `:=` binds only from its declaration point onward).
//
// So the battery asserts both, and a resolver that is merely conservative
// fails it just as a reckless one does.
// ---------------------------------------------------------------------------

type resolution struct {
	pkg, fn string
	line    int
	isConst bool // `pkg.Name` NOT in call position — a constant or var
}

// binding is a local name in scope from `pos` to the end of its block.
type binding struct {
	name string
	pos  token.Pos
	end  token.Pos // end of the scope that owns it
}

// resolveFile returns the package calls it can justify, honouring scope.
func resolveFile(fset *token.FileSet, f *ast.File) []resolution {
	imports := map[string]string{}
	for _, im := range f.Imports {
		path := strings.Trim(im.Path.Value, `"`)
		name := ""
		if im.Name != nil {
			if im.Name.Name == "_" || im.Name.Name == "." {
				continue
			}
			name = im.Name.Name
		} else {
			name = path
			if i := strings.LastIndex(name, "/"); i >= 0 {
				name = name[i+1:]
			}
			if i := strings.Index(name, "."); i > 0 {
				name = name[:i]
			}
		}
		imports[name] = path
	}

	var binds []binding
	// collect every local binding of a name that COLLIDES with an import
	ast.Inspect(f, func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.FuncDecl:
			if x.Body == nil {
				return true
			}
			// parameters, results and receiver bind over the whole body
			fields := []*ast.FieldList{x.Type.Params, x.Type.Results, x.Recv}
			for _, fl := range fields {
				if fl == nil {
					continue
				}
				for _, fd := range fl.List {
					for _, id := range fd.Names {
						if _, ok := imports[id.Name]; ok {
							binds = append(binds, binding{id.Name, x.Body.Pos(), x.Body.End()})
						}
					}
				}
			}
		case *ast.BlockStmt:
			// `:=` and `var` bind from the STATEMENT onward, to block end
			for _, st := range x.List {
				switch d := st.(type) {
				case *ast.AssignStmt:
					if d.Tok == token.DEFINE {
						for _, l := range d.Lhs {
							if id, ok := l.(*ast.Ident); ok {
								if _, isImp := imports[id.Name]; isImp {
									binds = append(binds, binding{id.Name, d.End(), x.End()})
								}
							}
						}
					}
				case *ast.DeclStmt:
					if gd, ok := d.Decl.(*ast.GenDecl); ok {
						for _, sp := range gd.Specs {
							if vs, ok := sp.(*ast.ValueSpec); ok {
								for _, id := range vs.Names {
									if _, isImp := imports[id.Name]; isImp {
										binds = append(binds, binding{id.Name, d.End(), x.End()})
									}
								}
							}
						}
					}
				}
			}
		case *ast.RangeStmt:
			for _, e := range []ast.Expr{x.Key, x.Value} {
				if id, ok := e.(*ast.Ident); ok {
					if _, isImp := imports[id.Name]; isImp {
						binds = append(binds, binding{id.Name, x.Body.Pos(), x.Body.End()})
					}
				}
			}
		}
		return true
	})

	shadowed := func(name string, at token.Pos) bool {
		for _, b := range binds {
			if b.name == name && at >= b.pos && at < b.end {
				return true
			}
		}
		return false
	}

	// Which selectors sit in CALL position. `pkg.F(x)` is a call;
	// `pkg.Name` alone is a constant or variable reference, and Go
	// distinguishes them — `bits.UintSize()` does not compile. So the
	// extractor must too, or the walker would be handed a `callPkg` node
	// naming something that is not a function (§G24).
	inCall := map[token.Pos]bool{}
	ast.Inspect(f, func(n ast.Node) bool {
		if ce, ok := n.(*ast.CallExpr); ok {
			if se, ok := ce.Fun.(*ast.SelectorExpr); ok {
				inCall[se.Pos()] = true
			}
		}
		return true
	})

	var out []resolution
	ast.Inspect(f, func(n ast.Node) bool {
		se, ok := n.(*ast.SelectorExpr)
		if !ok {
			return true
		}
		id, ok := se.X.(*ast.Ident)
		if !ok {
			return true
		}
		path, isImport := imports[id.Name]
		if !isImport || shadowed(id.Name, id.Pos()) {
			return true
		}
		out = append(out, resolution{
			pkg: path, fn: se.Sel.Name,
			line:    fset.Position(id.Pos()).Line,
			isConst: !inCall[se.Pos()],
		})
		return true
	})
	return out
}

func runResolveSelfTest() {
	type tc struct {
		name string
		src  string
		want []string // "path.Fn" expected, in order
	}
	cases := []tc{
		{"plain package call", `package p
import "math/bits"
func f(x uint64) int { return bits.Len64(x) }`, []string{"math/bits.Len64"}},

		{"aliased import", `package p
import b "math/bits"
func f(x uint64) int { return b.Len64(x) }`, []string{"math/bits.Len64"}},

		{"path tail differs from dir", `package p
import "encoding/json"
func f() { json.Marshal(nil) }`, []string{"encoding/json.Marshal"}},

		// --- the WRONG-ANSWER direction: must NOT resolve ---
		{"parameter shadows the import", `package p
import "math/bits"
func f(bits int) int { return bits.Len64(0) }`, nil},

		{"var shadows the import", `package p
import "math/bits"
func f() int { var bits int; _ = bits; return bits.Len64(0) }`, nil},

		{"short decl shadows the import", `package p
import "math/bits"
func f() int { bits := 0; _ = bits; return bits.Len64(0) }`, nil},

		{"range var shadows the import", `package p
import "math/bits"
func f(xs []int) { for _, bits := range xs { _ = bits.Len64(0) } }`, nil},

		// --- the TIMID direction: a use BEFORE the shadow MUST resolve ---
		{"use precedes the shadowing :=", `package p
import "math/bits"
func f(x uint64) int {
	n := bits.Len64(x)
	bits := 0
	_ = bits
	return n
}`, []string{"math/bits.Len64"}},

		{"shadow is in a SIBLING block, not this one", `package p
import "math/bits"
func f(x uint64) int {
	if x > 0 { bits := 0; _ = bits }
	return bits.Len64(x)
}`, []string{"math/bits.Len64"}},

		{"not an import at all", `package p
func f(x foo) int { return x.Len64() }`, nil},

		// --- the CONSTANT kind (§G24) ---
		{"package constant, not a call", `package p
import "math/bits"
func f() int { return bits.UintSize }`, []string{"const math/bits.UintSize"}},

		{"constant and call in one expression", `package p
import "math/bits"
func f(x uint) int { return bits.UintSize - bits.LeadingZeros(x) }`,
			[]string{"const math/bits.UintSize", "math/bits.LeadingZeros"}},

		{"a shadowed constant is still not resolved", `package p
import "math/bits"
func f(bits int) int { return bits.UintSize }`, nil},
	}

	pass, fail := 0, 0
	for _, c := range cases {
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, "t.go", c.src, parser.SkipObjectResolution)
		if err != nil {
			fmt.Printf("  FAIL  %-38s parse error: %v\n", c.name, err)
			fail++
			continue
		}
		got := []string{}
		for _, r := range resolveFile(fset, f) {
			if r.isConst {
				got = append(got, "const "+r.pkg+"."+r.fn)
			} else {
				got = append(got, r.pkg+"."+r.fn)
			}
		}
		ok := len(got) == len(c.want)
		if ok {
			for i := range got {
				if got[i] != c.want[i] {
					ok = false
				}
			}
		}
		if ok {
			fmt.Printf("  ok    %-38s -> %v\n", c.name, got)
			pass++
		} else {
			fmt.Printf("  FAIL  %-38s -> %v, want %v\n", c.name, got, c.want)
			fail++
		}
	}
	fmt.Printf("\nresolver self-test: %d passed, %d failed\n", pass, fail)
	if fail > 0 {
		os.Exit(6)
	}
}
