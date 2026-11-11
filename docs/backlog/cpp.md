# C++ lane backlog

## `cpp-target-profile-unchecked`: artifact profile gate

**Closed 2026-11-11.** The C++ extractor now validates Clang's recorded
predefined macros against the admitted LP64/signed-char profile (8-bit bytes,
16-bit short, 32-bit int, 64-bit long and long long, 64-bit pointers) and the
Lean artifact ingester applies the same check. `-m32`, `-m64`,
`-fsigned-char`, and `-funsigned-char` are refused instead of producing an
artifact evaluated under a different profile. `harness/cpp_profile_guard_test.py`
pins the default match and profile-changing-flag refusal.

## `cpp-switch-and-ir-lowering`: cleanup-node retention

**Partially closed 2026-11-11.** Callable admission now retains
`ExprWithCleanups` as an explicit `CallableStatement.cleanups` node, and both
callable evaluators execute its child while preserving the source boundary.
Switch bodies still use the existing clause representation; replacing that
regrouping with source `CaseStmt`/`DefaultStmt` items remains open.

## `c-name-resolution-by-string`: callee declaration-kind guard

**Partially closed 2026-11-11.** C call dispatch now uses the retained
`DeclRefExpr` declaration kind through `calleeName` and refuses local-variable
or indirect references before looking up a function by name. A local callee
row pins the refusal (the existing type-layout frontier may report first).
Full declaration-id threading for variables, globals, and function bodies
remains open.

## `cpp-diff-handwritten-twins`: reporting boundary

**Closed 2026-11-11 (reporting correction).** The harness and generated page
classify independent handwritten Lean/native checks as `WITNESS`; only the
verified TinyXML-2 capture path can produce `MATCH`. A regression test pins
that a generic callable row cannot become `MATCH` by matching values alone.
The broader source-derived capture pipeline remains separately documented as
open work and is not represented as a differential match.

## `cpp-call-arg-order`: effectful call arguments

**Closed 2026-11-11.** Direct-call admission now refuses any call argument
with observable effects, matching the existing binary-operand guard and
avoiding a fabricated left-to-right resolution for indeterminately sequenced
parameter initializations. `CallableTests` pins the refusal for a postfix
increment argument while the pure direct-call witness remains admitted.

## `cpp-diff-handwritten-twins`: source-derived differential execution

**Open.** The C++ coverage harness evaluates checked-in Lean fixtures while
Clang compiles separate source witnesses. Passing both is useful unit evidence,
but it does not show that Lean evaluated the compiled source's AST. The four
TinyXML-2 callable rows use a source-derived literal, whose provenance manifest
pins the inputs. The coverage harness verifies the native source, generated
literal, target ABI, and the bound call before crediting those rows. The grammar
census checks Clang's emitted node kind and records a refusal boundary; it does
not execute each grammar source in Lean.

The reporting correction classifies these independent passes as `WITNESS` and
keeps failing checks visible. To close the finding, capture each native source
with the pinned Clang frontend and canonical probe, admit and execute its
corresponding callable on the row's arguments, and compare its observed result
with the compiled original. Record loud refusals where the pipeline cannot
admit a source. Keep independent fixtures as unit witnesses, and run grammar
samples through the same source-to-model path before treating them as execution
results.

## `cpp-two-callable-evaluators`: one callable semantics

**Open.** The value and object evaluators still interpret the same callable IR
independently. Expression and restricted whole-call agreement theorems cover
selected fragments, not a general refinement or the full differential corpus.
Delete the duplicate evaluator by projecting the object semantics, or establish
a refinement for its full admitted domain, and run source-derived differential
rows through the evaluator used in the proofs.
