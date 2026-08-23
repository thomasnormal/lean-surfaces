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

var builtinNames = map[string]bool{
	"append": true, "cap": true, "clear": true, "close": true, "complex": true,
	"copy": true, "delete": true, "imag": true, "len": true, "make": true,
	"max": true, "min": true, "new": true, "panic": true, "print": true,
	"println": true, "real": true, "recover": true,
}

func main() {
	var paths []string
	var out, compare, root, ladder, kindsets string
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
			} else {
				c.Decls["func"]++
			}
			if x.Body == nil {
				c.Decls["func_no_body"]++
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
		case *ast.CallExpr:
			if id, ok := x.Fun.(*ast.Ident); ok && builtinNames[id.Name] {
				c.Builtins[id.Name]++
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
