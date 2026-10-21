# Procedural loops

IEEE 1800-2023 §12.7.1 orders a `for` loop as initializer, header
condition, body, and ordered steps. Initializers execute once. A missing
condition is true. A false or ambiguous condition exits; normal completion
and `continue` execute the step list before returning to the header.
`break` exits without running the steps (§12.8).

The legacy/self-check envelope retains `For.initializers`, `condition`,
`steps`, and `body` rather than unrolling a loop or synthesizing an index.
Assignment steps and discarded integral prefix/postfix increments and
decrements reuse the ordinary assignment and four-state arithmetic rules.
The implicit block for header-local variables retains its declarations;
the existing flat-state shadow and duplicate-name checks still apply.

`while` (§12.7.4) tests its condition before each body. `do…while`
(§12.7.5) enters the body first and tests only after completion or
`continue`. A known one bit makes an integral condition true even when
other bits are x/z; a condition with no known one bit exits. `break`
exits without evaluating the next test. Nested loops consume transfers at
their nearest boundary.

The envelope retains `While` and `DoWhile` nodes with their source
`condition` and `body`. Ingestion maps `While` to the existing `for` control
with empty initializer and step lists. A body-first `doWhileLoop` entry
handles the first body and then uses the same empty-step control for all
subsequent tests and iterations. No synthetic signal or unrolling is needed.

`foreach` (§12.7.3) traverses supported fixed unpacked and packed dimensions
in declared left-to-right order, with the rightmost named index varying
fastest. Omitted indices do not traverse their dimension; omitting every
index executes the body once. The source's implicit iterators are signed
32-bit integers with automatic scope. Stable declaration-based names keep
same-name outer variables and nested loops distinct, and a module-wide
collision audit rejects generated storage aliases.

The extractor compiles the finite index space to one existing `For` with an
unsigned ordinal and quotient/remainder index bindings. It retains dimension
bounds as provenance. One loop boundary makes `break` exit every dimension;
`continue` advances exactly one tuple. Reentry resets the automatic bindings.
Array reads remain live, including across a retained delay. No new evaluator,
array store or scheduler is introduced. Unsupported aggregate storage,
dynamic/queue/associative arrays, unmodelled body lifetimes, invalid source,
and symbolic-mode loops stay loud; the ordinal cardinality must fit 32 bits.

Noncanonical packed element reads with a pure signed 32-bit index normalize
the declared label to the existing LSB offset after widening to 34 bits
(§11.5.1). This preserves signed bounds without wrapping an invalid index
into a valid bit. Unknown/out-of-range indices use the source state kind's
existing x/zero result. Other runtime index types and noncanonical dynamic
selected writes retain their prior boundary. A wide unsigned negative-bound
probe remains a deliberate refusal because independent observations disagree
with a mathematical-offset interpretation; no truncation rule is guessed.

The foreach source fixtures check complete independently observed output,
including mixed dimensions, omissions, transfers, reentry, shadowing, signed
bounds and live delayed reads. Kernel proofs bound to an extracted tuple
loop establish its quotient/remainder offsets, coordinate coverage and
whole-loop break at the retained body boundary.

`repeat` (§12.7.2) samples its count once, retains a remaining count, and
decrements it after normal body completion or `continue`. The sampled
integral value is first converted to a signed 32-bit count: x/z bits become
zero, source signedness controls extension before narrowing, and a converted
nonpositive value executes no body. This includes unknown counts and values
whose low 32 bits have the sign bit set; they do not create an unbounded
runtime loop or a fabricated error.

The source-owned conversion rule is therefore executable and explicit in
`evalForCondition` and `sampleRepeatCount`: evaluate the count expression once
at loop entry, preserve its elaborated width and signedness through the
32-bit conversion, and map a converted nonpositive value to zero. No resumed
body or loop boundary evaluates the count expression again. For loops use the
analogous source-order rule: initializer statements run once, each header
condition is evaluated at the header, and each completed body or `continue`
runs the step list once before the next header.

## Public source-phase contract

The source layer exposes the phase ordering directly. A legal `for` transition
is one of the following, in order:

| phase | next phase after normal completion |
|---|---|
| initializer list | header condition |
| header condition, true | body |
| header condition, false or ambiguous | loop exit |
| body, including `continue` | ordered step list |
| ordered step list | header condition |

`break` moves directly to loop exit and never evaluates the step list. A
`repeat` transition evaluates its count once, samples a nonnegative remaining
counter, and enters the body only while that counter is positive. Normal body
completion and `continue` each consume one iteration; `break` exits without a
further decrement. An ordinary dependency wait retains the current phase and
the complete continuation, so resumption cannot rerun an initializer,
condition already completed, step, or count sample.

The repeat count conversion is the IEEE integral conversion written as a
total rule over the admitted source values:

1. map every `x`/`z` bit to `0`;
2. sign-extend or zero-extend according to the source expression's signedness;
3. narrow to signed 32 bits; and
4. use zero iterations when the converted value is nonpositive, otherwise use
   its natural count.

Malformed, effectful, or otherwise unrepresented source evaluation remains a
loud refusal. Explicit process-control suspension and wait rearming are also
outside this contract until their kernel rule is supplied; they must not be
approximated by restarting a loop.

The process-local stepper stores the unfinished body followed by a loop
boundary marker. An ordinary delay or event wait retains the current
state, output, pending nonblocking work, and the loop's next phase.
Resumption does not rerun initialization or sample a repeat count again.
A resumed `continue` discards the unfinished body tail but still reaches
the saved boundary. Nested loops consume transfers at their nearest
boundary. The existing scheduler receives the same retained statement-list
interface; no region choice, new queue, or second scheduler is introduced.
The first `do…while` body uses that same retained body boundary, so a wait
resumes the body before its first post-test. The completed-step
correspondence includes this body-first entry.

The timed loader refuses a design when a source process can write a signal
watched by any edge wait, including an implicit clocked-process wait. The
current kernel delivers external stimulus edges but does not publish each
procedural blocking/NBA edge. Comparing whole-body before/after states would
lose intermediate edges, so it is not used as a substitute. The admission
scan includes ordinary and selected assignments, packed targets, scanner
copyback, declarations, branches and loop phases. This conservative guard
prevents silent loss of a waiting continuation; it adds no scheduler rule.

The general executor/stepper correspondence now covers loop phases.
Three original source fixtures check header ordering, sampled counts,
signedness, transfers, and nesting. Their complete output is independently
confirmed. The actual ordered-header subtree is checked against the
extracted source and has a kernel proof; dependency-wait witnesses check
retained phases and transfers across multiple resumes.

Effectful conditions/counts, function-call steps, repeated-body local
declarations with unmodelled lifetime, symbolic `sv-0.2` loops, and explicit
process-control suspension/rearming remain loud. The self-check runner
still executes initial-only programs at time zero; ordinary timed source
statements are not newly admitted by this extraction family.

`forever` (§12.7.6) repeats its body without a source condition, initializer
or step. The envelope retains `Forever.body`; ingestion compiles it to the
existing `forLoop` with a one-bit true condition and empty initializer and
step lists. Normal completion and `continue` enter the next iteration;
`break` exits the nearest loop, and `$finish` halts the run. A body that runs
forever without suspending exhausts fuel with `timeout`, never successful completion.

Delay and event waits use the same retained body tail and loop boundary as
other procedural loops. Resume finishes that body before starting the next
iteration; a completed event body rearms its wait through the next iteration.
The authored forever fixtures check finite transfers, nesting, automatic
array reinitialization, live four-state payloads across delays and a blocked
event body. Their kernel proofs bind to exact compiled source subtrees.
No scheduler rule or evaluator constructor is added. Named-block `disable`,
procedural edge publication, timed clock queries, zero-delay Inactive delivery,
unsupported declaration lifetimes and symbolic-mode loops retain their existing
refusals.

Static scalar declarations initialize once before process entry; actual automatic
scalars initialize at each fresh sequential entry and retain their values through
saved dependency-wait continuations. See
[procedural lifetimes](sv-procedural-lifetimes.md) for initialization boundaries.
