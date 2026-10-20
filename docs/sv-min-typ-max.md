# Min typ max expressions

IEEE 1800-2023 §11.11 and §10.8 define a min/typ/max expression as three
alternatives with one elaboration-selected expression. The legacy extractor
uses typical by default. `--min-typ-max min|typ|max` sets the frontend's global
choice, including parameter widths, generate decisions and nested choices.
These names select positions; the values are not sorted or compared.

The extractor retains the frontend's complete selected bound expression,
including width, signedness and context conversions. `MinTypMax` records
`choice`, positive `width`, optional `signed`, and the selected `value`.
The loader validates the choice and matching width, then parses the selected
operand directly. Existing expression evaluation, blocking/NBA stores and
timers give the selected program its meaning. No evaluator branch or scheduler
is added. An ordinary assignment conversion still surrounds the selected tree
when required; choosing an arm does not sample a live signal at elaboration.

Only the selected arm participates in source-purity, unresolved numeric-call,
constant-context, package-initializer and array-alias analyses. Unselected
increments and unknown `$clog2` calls neither execute nor poison admission.
Frontend validity still covers the whole compilation. Errors and redefinitions
in a design containing a surviving min/typ/max expression refuse explicitly.
Selected effects, unsupported types/calls and other existing expression limits
remain loud. Symbolic constant folding retains its previous behavior;
nonconstant symbolic min/typ/max remains unsupported, and nondefault symbolic
CLI choices refuse. This item does not extend symbolic elaboration.

The literal-delay converter can unwrap a selected integral literal and call
the existing delay rule. A selected dynamic delay, unsupported units or other
existing delay restrictions still refuse. The authored timing fixture observes
choices 2/5/8 against markers at 3/7 under both region oracles. One new corpus
extraction still refuses timed execution because it contains the existing
time-zero-only `$time` lowering; this is not a successful simulation claim.

The frontend rejects a direct min/typ/max expression in one display argument
context accepted by the reference. `argument_context.sv` preserves the exact
source and all three independent observations. It remains loud through
`InvalidStatement`; successful fixtures assign the selected value before
printing. No agreement is claimed for this frontend boundary.

Nondefault envelopes append `min_typ_max` at the top level; absent means
`typ`. Reproduction must pass the recorded mode back to extraction. Default
envelopes keep their existing metadata layout. Exact same-mode CLI replay is
tested for all three choices. Only default example envelopes are committed;
the CI-owned roundtrip harness's nondefault replay update has been requested.

The paired 22,035-path census gains 15 clean extractions without losses:
4,098 clean, 17,871 partial, 66 include skips, zero extraction errors. All
11 originally priced min/typ/max rows match complete reference transcripts
under both region oracles. Four further gains involve pattern members,
replication and literal delays; together the 15 gains produce 14 complete
matches and the named `$time` refusal above. Of 4,083 previously clean designs,
one changes from a folded constant into the explicit selected tree; its old
and new executions both match the same complete reference transcript.
Extraction counts include negative and compile-only inputs and do not measure
whole-corpus runtime conformance.

Thirty authored mode/source pairs produce 20 complete both-oracle matches
and 10 explicit refusals. At the default choice, eight complete transcripts
match both oracles and six also match time-zero execution. Five kernel
theorems bind the actual parsed blocking and NBA statements in `runtime.sv`:
live selected reads, unselected-value independence, blocking storage preserving
pending work/output, NBA capture and stability after a later source change.
They prove properties of the selected parsed program, rather than correctness
of the frontend selection algorithm. See the [fixtures and receipts](../Examples/system-verilog/min_typ_max/README.md).
