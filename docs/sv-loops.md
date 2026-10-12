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
decrements it after normal body completion or `continue`. Count width and
signedness are preserved from the bound expression. Known signed negative
counts execute no body. Runtime admission currently requires a known
nonnegative count at most 2,147,483,647; wider values within that range are
admitted. Unknown counts and larger nonnegative values refuse loudly.
The standard specifies zero iterations for x/z counts, but that boundary
is not claimed as implemented by this tier.

The source-owned conversion rule is therefore explicit: evaluate the count
expression once at loop entry, preserve its elaborated width and signedness,
map a known signed-negative value to zero, and otherwise convert only a known
nonnegative integral value in the admitted range. No resumed body or loop
boundary evaluates the count expression again. For loops use the analogous
source-order rule: initializer statements run once, each header condition is
evaluated at the header, and each completed body or `continue` runs the step
list once before the next header.

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
