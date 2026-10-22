# Simple immediate assertion actions

IEEE 1800-2023 §16.3 simple immediate `assert` and `assume` evaluate their
current condition once, executing the success action for logical true and
the failure action otherwise. The simulation tier treats immediate `assume`
as an assertion check. Immediate `cover` runs its success action when the
condition is true and has no failure action or diagnostic.

The legacy extractor lowers these checks to the existing `If` statement,
retaining `immediate_assertion` (`assert`, `assume` or `cover`) and
`assertion_lowered` provenance. Conditions use the admitted pure integral
fragment. Any definite one bit makes a vector true; zero and vectors with
only zero/X/Z bits fail. Calls or increments cannot disappear through
frontend constant folding. Actions use the ordinary statement executor in
source order. Explicit empty blocks retain their meaning. A selected action
that waits keeps its unfinished tail; resumption does not recheck a changed
condition. No interpreter constructor or scheduler rule is added.

Omitting an `assert`/`assume` failure action requests the standard's implicit
error diagnostic. That branch becomes `Unsupported` with the
`ImmediateAssertion:implicit-error` tag. A true run can finish, but the file
remains partial in the extraction census; a failure refuses loudly. Diagnostic
text, error status and coverage databases are not fabricated. Assertion-control
and coverage-query calls retain their own refusals.

Deferred `#0`/`final` and concurrent checks require their region/sampling
semantics and remain loud. Unsupported conditions and action statements,
symbolic-mode checks and invalid source also remain loud. A design with
frontend errors containing the new lowering is refused at design level.
Null failure actions (`assert (p) else;`) are a separate validation boundary:
the frontend accepts them but the independent compiler rejects them. They
remain `ImmediateAssertion:null-failure`; explicit empty `begin end` actions
are admitted. A dedicated fixture preserves the disagreement.

## Implicit diagnostic subfamily — 2026-10-22

The fresh 22,043-path census records `ImmediateAssertion:implicit-error` in
25 files; **22** are implicit-error-only and **3** co-occur with another wall.
The read-only repricer finds **24** implicit diagnostic branches in the sole
files: 17 `assert` and seven `assume` branches, 12 omitted success actions,
12 explicit success actions, five named assertions, 13 definite-true
conditions, one definite-false condition, two ordinary `always` contexts and
one `always_comb` context (features overlap). These rows include compile-only
chapter-37 metadata files. The branch remains an explicit unsupported else
node: no diagnostic text, status, source-location footer or coverage database
is invented. Reproduce the measurement with
`extractors/sv/immediate_assert_error_reprice.py`.

Independent checks pin four-state mode, enable cover directives and every
cover success, and disable additional assertion-engine status messages:
`-ii_val -abvcoveron -abvrecordcoverall -abvdisableasrtst`. Default simulator
configuration disables covers and adds status reports even for explicit
failure actions. Those default transcripts are retained as evidence of the
configuration boundary. No additional transcript filtering is applied.
The implicit-error fixture uses ordinary four-state mode and confirms a real
diagnostic; it is a refusal, not an execution match.

The paired 22,035-path census gains 40 clean files with no losses. Thirty-five
gains match complete independent transcripts under both region oracles.
Four gains retain runtime refusals: internal procedural-edge publication,
time-zero-only clock queries, scope-aware `%m` rendering and `always_comb`.
One more runs the correct assertion actions but differs in the independent
`$finish(0)` source-location footer; the model only emits the source's `PASS`.
That observation difference remains documented, not counted as agreement.

Four authored runnable sources agree completely under both oracles, covering
all sixteen two-bit four-state conditions, nested actions, wide truthiness,
explicit empty blocks, successful implicit checks and selected delayed actions
whose conditions change while waiting. Three further fixtures preserve the
implicit diagnostic, deferred-region and null-failure boundaries. Four kernel
theorems bind to exact parsed source subtrees and establish current-value
evaluation, retained success/failure tails and unsuccessful-cover behavior.
