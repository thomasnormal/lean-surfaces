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
