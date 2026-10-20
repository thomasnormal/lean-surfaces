# Plain always procedures

IEEE 1800-2023 §9.2.2.1 starts a plain `always` procedure at time zero and
repeatedly executes its complete statement. The legacy envelope retains an
`Always` process with that source body. `SelfCheck.SProc.alwaysBody` preserves
the distinction from `initial`; the initial-only, time-zero `runSelfCheck`
refuses it even when an earlier initial process calls `$finish`.

`timedProcOf` compiles one such process into one ready process whose residual
is the existing `forLoop` with empty initializer/step lists and a one-bit true
condition. It has no separate `arm`. `stepForLoop` executes the source body;
normal completion starts its next iteration. A delay or event wait retains
the unfinished body tail followed by `forAfterBody`. Resumption finishes that
body before entering the next iteration. No artificial yield, process, queue,
or scheduler is added. A non-suspending infinite body exhausts fuel rather
than reporting successful completion.

The canonical top-level `always @(posedge signal)` encoding remains
`AlwaysPosedge`, using its existing wait/body/arm representation. Bare and
negative-edge controls in the new general body use existing `WaitEvent`
nodes. Implicit sensitivity, event lists, `iff`, level `wait` statements and
unsupported control/body forms retain their refusals. `always_ff`,
`always_comb`, `always_latch` and the symbolic schema keep their existing
separate boundaries. Invalid frontend compilations containing the lowering
are refused, so synthetic repetition cannot legitimize an illegal source
`break` or `continue`.

Scalar body declarations with unmodelled repeated lifetime remain loud.
Already-admitted automatic fixed-array cells reinitialize on each body entry.
The timed loader scans the new bodies for internally written edge sources
and retains its procedural-publication barrier. Time-zero-only clock queries
and zero-delay Inactive delivery also remain loud.

The authored fixtures check time-zero prefixes, retained delayed tails and
live four-state values, independent process periods, automatic array
reinitialization in an always-only design, and permanently blocked bare and
negative-edge waits. Four complete transcripts agree with an independent
simulator under both region oracles. A fifth fixture preserves the internal
edge-publication refusal. Four kernel theorems, bound to actual parsed source
bodies, establish the single-process compilation and delay/event retention
and rearming rules; their axioms are printed in the proof file.

The paired 22,035-path census gains 90 clean files with no losses. Six gains
match independent complete transcripts under both oracles. A seventh has a
race at time five: the fast counter update and the observing `$finish` process
are both ready in Active. The independent transcript and reverse oracle say
`PASS`; the source oracle says `FAIL: fast_count=5 slow_count=2`. This is
recorded separately, without changing either scheduler oracle. The remaining
83 gains are runtime refusals: 75 require procedural edge publication, six
use time-zero-only clock lowering, and two contain continuous assignments.
Two of the 75 are negative compilation fixtures that the independent
implementation also rejects; they are not execution matches.
Extraction coverage is separate from runtime agreement.
