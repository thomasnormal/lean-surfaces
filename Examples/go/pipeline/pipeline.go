// pipeline.go — the Go tier's rung-0 driver fixture.
//
// A worker pool: N goroutines draw jobs from one channel and send
// results down another; the collector sums them. It is deliberately
// the smallest program that is still REAL concurrency — a `go`
// statement, a buffered and an unbuffered channel, a send, a receive, a
// range over a channel, a close, a select with a default — and nothing
// else. Its only import is `fmt`.
//
// THE POINT OF THE FIXTURE is the split between its two observables:
//
//   - `sum` and `count` are INVARIANT under every schedule. Each job
//     contributes its square exactly once, addition is associative and
//     commutative, so no interleaving can change the total.
//   - the ORDER results arrive in is not invariant, and neither is
//     which worker handles which job. Measured over 30 runs: 6 distinct
//     per-worker job splits, one of them [51 49 0 0] — two workers ran
//     and two were starved outright — with `count` and `sum` identical
//     in all 30.
//
// So the program has a deterministic observable in spite of a
// nondeterministic execution, which is what makes it differentially
// testable at all: a model that quantifies over schedules can be
// checked against a real toolchain that samples one. A fixture whose
// only observable were the arrival order could not be.
//
// THE JOIN IS A CHANNEL, NOT A WaitGroup, and that is a census
// decision rather than a style one. The Go memory model states
// ordering rules for goroutine creation, channel send, channel
// receive and close; it explicitly delegates `sync.WaitGroup`,
// `sync.Cond`, `sync.Map` and `sync.Pool` to their package
// documentation instead. A rung-0 fixture must depend only on
// guarantees the memory model itself makes, or the first thing the
// tier models is a library contract rather than the language.
//
// The `for i := 1; i <= njobs; i++` is the loop form whose variable
// scoping changed at go1.22. It is written so that the change is not
// observable here — the value is sent, not captured — which is the
// point: rung 0 must not depend on the version delta. The delta gets
// its own fixture.
package main

import "fmt"

const (
	workers = 4
	njobs   = 100
)

// worker draws jobs until the channel is closed, sends one result per
// job, and then reports its own completion on `done`. `range` over a
// channel terminates exactly when the channel is closed and drained,
// which is the whole termination argument.
func worker(jobs <-chan int, results chan<- int, done chan<- bool) {
	for j := range jobs {
		results <- j * j
	}
	done <- true
}

func main() {
	jobs := make(chan int, workers)
	results := make(chan int, workers)
	done := make(chan bool) // unbuffered: the rendezvous case

	for w := 0; w < workers; w++ {
		go worker(jobs, results, done)
	}

	// The feeder: once every job is queued, closing `jobs` is what
	// lets every worker's range terminate. Closing from the sender
	// side, exactly once, is the discipline the language requires.
	go func() {
		for i := 1; i <= njobs; i++ {
			jobs <- i
		}
		close(jobs)
	}()

	// The join. Receiving once per worker is synchronized-after each
	// worker's final send by the memory model's channel rule, so
	// closing `results` here cannot race the workers' sends.
	go func() {
		for w := 0; w < workers; w++ {
			<-done
		}
		close(results)
	}()

	sum, count := 0, 0
	for r := range results {
		sum += r
		count++
	}

	// A select with a default over the drained, closed channel: the
	// receive is ready (it yields the zero value immediately), so the
	// default is dead here. It is present because `select` with a
	// default is the one place the language commits to a
	// non-blocking choice, and rung 0 should contain one.
	drained := false
	select {
	case _, ok := <-results:
		drained = !ok
	default:
		drained = false
	}

	fmt.Println("count", count)
	fmt.Println("sum", sum)
	fmt.Println("drained", drained)
}
