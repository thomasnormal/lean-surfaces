# Procedural for and repeat loops

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
