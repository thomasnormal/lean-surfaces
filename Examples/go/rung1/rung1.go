// rung1.go — the Go tier's rung-1 driver fixture.
//
// Rung 0 (Examples/go/pipeline/pipeline.go) is 28 AST node kinds and
// covers 512 of the standard library's 5,419 files (9.4%). This fixture
// adds the seventeen kinds the reach ladder identified as the top slice
// — control flow, composite values, parenthesisation and declarations —
// taking the modelled vocabulary to 45 kinds and 3,084 files (56.9%).
//
// The seventeen, and why they are one rung rather than four:
//
//	CONTROL  ReturnStmt IfStmt BranchStmt SwitchStmt CaseClause
//	         EmptyStmt LabeledStmt
//	VALUES   StarExpr ArrayType CompositeLit KeyValueExpr IndexExpr
//	         SliceExpr StructType
//	PAREN    ParenExpr
//	DECLS    DeclStmt TypeSpec
//
// COVERAGE IS CONJUNCTIVE, and that is the measurement that shaped this
// rung. A file is reachable only when EVERY kind it uses is modelled, so
// bundles do not compose additively: alone, VALUES buys 13.4% and
// CONTROL 13.2%, but together with PAREN and DECLS they buy 56.9%.
// Shipping any one of them alone would have bought almost nothing.
//
// The sharpest instance, and it reproduces the C tier's finding exactly
// (docs/c23-goal.md §4, where `SwitchStmt` alone cleared zero tests):
// adding `SwitchStmt` to rung 0 unlocks NOTHING, 512 files before and
// after; adding `CaseClause` alone likewise 512; adding BOTH unlocks
// 514. Two files. The switch family only pays once the rest of the rung
// is present, which is precisely why it is IN this rung and not its own.
//
// WHAT THIS FIXTURE PRESERVES FROM RUNG 0: the split observable. `total`
// and `count` are invariant under every schedule — each job contributes
// exactly once and addition commutes — while arrival order and the
// per-worker split are not. A deterministic observable over a
// nondeterministic execution is what makes the fixture differentially
// testable at all.
//
// Its only import is `fmt`, and the join is a counted channel receive
// rather than a sync.WaitGroup, for the reason rung 0 records: the Go
// memory model states rules for channels and delegates WaitGroup to
// package documentation.
package main

import "fmt"

// TypeSpec + StructType: a named record type.
type job struct {
	id   int
	kind int
	data []int
}

// TypeSpec over a non-struct underlying type.
type tally struct {
	sum   int
	seen  int
	byKnd [4]int // ArrayType with a constant length
}

const (
	workers = 3
	njobs   = 60
)

// classify uses a switch whose cases return — SwitchStmt + CaseClause +
// ReturnStmt. The default arm is what makes the function total.
func classify(n int) int {
	switch {
	case n%15 == 0:
		return 3
	case n%5 == 0:
		return 2
	case n%3 == 0:
		return 1
	default:
		return 0
	}
}

// score walks a slice with a labeled loop, a continue and a break —
// BranchStmt in both spellings, LabeledStmt, IfStmt, SliceExpr,
// IndexExpr, ParenExpr.
func score(xs []int) int {
	var acc int // DeclStmt
scan:
	for i := 0; i < len(xs); i++ {
		v := xs[i] // IndexExpr
		if v < 0 {
			continue
		}
		// ParenExpr: the grouping is load-bearing for the reader even
		// where precedence would allow it to be dropped.
		acc += (v * 2) + 1
		if acc > 1<<20 {
			break scan
		}
	}
	// A tail slice, re-scored — SliceExpr.
	if len(xs) > 2 {
		for _, v := range xs[1:] {
			if v > 0 {
				acc += v
			}
		}
	}
	return acc
}

// accumulate takes a POINTER to the tally — StarExpr, both as a type and
// as a dereference.
func accumulate(t *tally, j job, s int) {
	t.sum += s
	t.seen++
	if j.kind >= 0 && j.kind < len(t.byKnd) {
		t.byKnd[j.kind]++
	}
}

func worker(jobs <-chan job, results chan<- int, done chan<- int) {
	var local tally // DeclStmt of a named struct type
	for j := range jobs {
		s := score(j.data)
		accumulate(&local, j, s)
		results <- s
	}
	done <- local.seen
}

func main() {
	jobs := make(chan job, workers)
	results := make(chan int, workers)
	done := make(chan int)

	for w := 0; w < workers; w++ {
		go worker(jobs, results, done)
	}

	go func() {
		for i := 1; i <= njobs; i++ {
			// CompositeLit + KeyValueExpr: a keyed struct literal.
			j := job{
				id:   i,
				kind: classify(i),
				data: []int{i, i + 1, i + 2},
			}
			jobs <- j
		}
		close(jobs)
	}()

	go func() {
		for w := 0; w < workers; w++ {
			<-done
		}
		close(results)
	}()

	total, count := 0, 0
	for r := range results {
		total += r
		count++
	}

	// A dereference through a pointer to a local — StarExpr as an
	// expression rather than a type.
	final := &tally{sum: total, seen: count}
	snapshot := *final

	// A select with a default over the drained, closed channel, carried
	// forward from rung 0: a rung must be a SUPERSET of the one below
	// it, and dropping `select` here would have narrowed the modelled
	// vocabulary while appearing to widen it. The census caught exactly
	// that — this fixture's first version scored 43 kinds, not 45.
	drained := false
	select {
	case _, ok := <-results:
		drained = !ok
	default:
		drained = false
	}

	fmt.Println("drained", drained)
	fmt.Println("count", snapshot.seen)
	fmt.Println("total", snapshot.sum)
	fmt.Println("classes", classify(15), classify(10), classify(9), classify(7))
	goto end

	// LabeledStmt whose statement is an EmptyStmt — the idiomatic reason
	// an EmptyStmt node exists at all, and rare: 4 of the standard
	// library's 5,419 files use one.
end:
}
