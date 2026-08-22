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
	var out, compare, root string
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
		default:
			paths = append(paths, args[i])
		}
	}
	if len(paths) == 0 {
		die(2, "usage: construct_census.go <path>... [-o out.json] [--compare ref.json]")
	}

	files, err := collect(paths)
	if err != nil {
		die(2, err.Error())
	}
	if len(files) == 0 {
		die(2, fmt.Sprintf("no .go files found under %v", paths))
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
			if x.Tok == token.DEFINE {
				c.RangeOver["declares_vars"]++
			}
		case *ast.ForStmt:
			if a, ok := x.Init.(*ast.AssignStmt); ok && a.Tok == token.DEFINE {
				// The loop form whose scoping CHANGED at go1.22.
				c.RangeOver["for_clause_declares_vars"]++
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
