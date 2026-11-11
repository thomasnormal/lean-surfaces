# C++ lane backlog

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
