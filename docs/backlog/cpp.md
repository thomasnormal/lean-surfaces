# C++ lane backlog

## `cpp-target-profile-unchecked`: artifact profile gate

**Closed 2026-11-11.** The C++ extractor now validates Clang's recorded
predefined macros against the admitted LP64/signed-char profile (8-bit bytes,
16-bit short, 32-bit int, 64-bit long and long long, 64-bit pointers) and the
Lean artifact ingester applies the same check. `-m32`, `-m64`,
`-fsigned-char`, and `-funsigned-char` are refused instead of producing an
artifact evaluated under a different profile. `harness/cpp_profile_guard_test.py`
pins the default match and profile-changing-flag refusal. Revalidated
2026-11-11 under the 24 GiB cgroup with pinned Clang/LLVM 21.1.8:
`cpp-lp64-profile MATCH` and `cpp-profile-changing-flag REFUSE`.

## `cpp-switch-and-ir-lowering`: source-item switch semantics

**Closed 2026-11-11.** Callable admission retains `ExprWithCleanups` as an
explicit `CallableStatement.cleanups` node, and both callable evaluators
execute its child while preserving the source boundary. Switch admission now
retains each source `CaseStmt`, `DefaultStmt`, and ordinary sibling as a
`CallableSwitchItem` in frontend order, with its source handle and its own body;
it no longer groups statements into synthetic clauses. Both callable
evaluators select a matching label and execute the retained suffix for faithful
fallthrough, and kernel guards pin the source-item shape and sibling boundary.
The older clause constructor remains only for existing hand-built evaluator
fixtures; source admission and execution use the direct item representation.
Revalidated 2026-11-11 with the 24 GiB cgroup: `lake build
LeanModels.Cpp.CallableTests LeanModels.Cpp.TranslationTests
LeanModels.Cpp.CallableObjectEvaluationTests` completed successfully (26
jobs), including the source-item and cleanup guards.

## `c-name-resolution-by-string`: declaration-id resolution

**Closed 2026-11-11.** The C extractor now retains Clang declaration handles
on `FunctionDecl`, `VarDecl`, `ParmVarDecl`, `EnumConstantDecl`, and every
`DeclRefExpr`. The ingested AST carries those handles as structured
`DeclarationId` values. Function frames and globals bind an identity
environment, lvalues resolve object references by handle, enum constants use
handle-keyed bindings, and direct calls dispatch through the referenced
`FunctionDecl` handle. Name lookup remains only as a compatibility path for
old hand-built AST fixtures and the public `callByName` entry point; extracted
program semantics no longer redoes declaration lookup by spelling. The schema
table, C runners, and a compiled two-function/local-shadow probe cover the
new identity path. Revalidated 2026-11-11 with pinned Clang/LLVM 21.1.8:
`local-variable-callee REFUSE` from the identity guard.

## `cpp-spelling-identity`: structured base and result identity

**Partially closed 2026-11-11.** Enum and class admission no longer accepts a
qualified spelling merely because it ends with the expected bare name.
Class-base names now come from the retained structured record declaration
handle in `CppTypeEvidence`, and enum member-call result matching rejects
qualified suffixes instead of accepting a spelling-only identity. Exact
unqualified spellings remain admitted. Friend-class admission now refuses
until Clang's friend target handle is retained; setter and remaining enum
parameter checks now use the retained structured enum handle and preserve
qualified source spellings as data. Direct enum arguments still await a probe
handle join before their source spelling can be removed from the legacy
boundary; the new `admitWithTypeEvidence` path performs that join and accepts
qualified spellings. Revalidated 2026-11-11 with the 24 GiB cgroup:
`lake build LeanModels.Cpp.ClassSubobjects LeanModels.Cpp.MemberCallTests`
completed successfully (18 jobs), including the structured-handle guards and
friend-class refusal.

## `cpp-harness-oracle-misfile`: native oracle policy

**Closed 2026-11-11.** Native assertion failures are classified as `DIVERGE`,
while compile/run/environment failures remain `ORACLE`; the harness prints the
pinned Clang version and now requires an available pinned oracle by default.
Exploratory reports can opt out with `--allow-oracle`, but qualification runs
cannot pass with missing oracle evidence.

## `cpp-diff-handwritten-twins`: reporting boundary

**Closed 2026-11-11 (reporting correction).** The harness and generated page
classify independent handwritten Lean/native checks as `WITNESS`; only the
verified TinyXML-2 capture path can produce `MATCH`. A regression test pins
that a generic callable row cannot become `MATCH` by matching values alone.
The broader source-derived capture pipeline remains separately documented as
open work and is not represented as a differential match. Revalidated
2026-11-11 with the eight `test_cpp_diff_classification.py` cases and
`test_cpp_diff_reporting.py` (all passed); `tools/docs_check.py` also passed.

## `cpp-call-arg-order`: effectful call arguments

**Closed 2026-11-11.** Direct-call admission now refuses any call argument
with observable effects, matching the existing binary-operand guard and
avoiding a fabricated left-to-right resolution for indeterminately sequenced
parameter initializations. `CallableTests` pins the refusal for a postfix
increment argument while the pure direct-call witness remains admitted.
Revalidated 2026-11-11 with `lake build LeanModels.Cpp.CallableTests` under
the 24 GiB cgroup (18 jobs, exit 0).

## `cpp-diff-handwritten-twins`: source-derived differential execution

**Partially closed 2026-11-11.** The bounded TinyXML-2 callable path now
requires the current canonical literal gate whenever
`LEANCPP_TINYXML2_PROBE` is supplied, in addition to the pinned source,
literal, ABI and call-binding checks. A missing probe keeps those rows
`ORACLE`; a stale or mismatched probe cannot produce `MATCH`. The C++ coverage
harness still evaluates checked-in Lean fixtures while
Clang compiles separate source witnesses. Passing both is useful unit evidence,
but it does not show that Lean evaluated the compiled source's AST. The four
TinyXML-2 callable rows use a source-derived literal, whose provenance manifest
pins the inputs. The coverage harness verifies the native source, generated
literal, target ABI, and the bound call before crediting those rows. The grammar
census checks Clang's emitted node kind and records a refusal boundary; it does
not execute each grammar source in Lean.

The reporting correction classifies these independent passes as `WITNESS` and
keeps failing checks visible. To close the remaining generic finding, capture each native source
with the pinned Clang frontend and canonical probe, admit and execute its
corresponding callable on the row's arguments, and compare its observed result
with the compiled original. Record loud refusals where the pipeline cannot
admit a source. Keep independent fixtures as unit witnesses, and run grammar
samples through the same source-to-model path before treating them as execution
results.

## `cpp-two-callable-evaluators`: one callable semantics

**Closed 2026-11-11.** `evaluateCallable` is now a value-shaped projection of
the frame-backed `CallableObjectEvaluation.evaluateCallableObject`; it no longer
interprets the callable tree a second time. The former list-state implementation
is retained as the explicitly named `evaluateCallableValue` compatibility
evaluator for its existing expression/refinement lemmas, while the public
entry point and object-backed callable differential rows use the object
evaluator.
`evaluateCallable_ok_value_iff` records the successful-result projection and
`evaluateCallable_unsupportedCall_iff` pins the single `unsupportedCall`
diagnostic. Existing whole-call refinement theorems now name the compatibility
evaluator explicitly, so their scope is honest. The frame evaluator's call arm
remains a loud boundary with its own cause.

## `c-no-compiled-oracle`: pinned C differential battery

**Closed 2026-11-11.** Added `harness/c_diff_test.py` and its five-row
`harness/c_cases.json` battery. Each row compiles the unchanged C source with
the full pinned Clang/LLVM 21.1.8 build line, `-std=c23 -O0 -g
-D_FORTIFY_SOURCE=0 -fno-strict-aliasing`, extracts that same source, and runs
the envelope through the Lean C model. Native signed-overflow sanitizer rows
are recorded as model `REFUSE`; value rows compare the model's mathematical
return with the native exit projection. Missing or unpinned compilers are
`ORACLE` and fail the default run unless `--allow-oracle` is explicit.
`extract.py` now selects `LEAN_C_CLANG`, refuses any other full version line,
and stamps that line into the envelope. The Lean ingester retains and checks
`frontend.version` against the same pin, so a family-only stamp cannot admit an
envelope produced by a different point release. `harness/c_profile_probe.py`
uses the same executable selection.

## `c-census-regex`: AST/preprocessor census inputs

**Closed 2026-11-11.** `harness/c_frontend.py` now owns the source-attributed
Clang AST and preprocessor walks. `c_construct_census.py` derives includes,
macro counts, function storage and all construct facts from those streams;
`c_suite_census.py` derives includes/directives from preprocessor output and
node/call/format facts from the AST; `c_api_census.py` derives API references,
libc calls, floating use, and static objects from AST nodes plus the
source-attributed macro stream. The previous source regexes and the
non-reproducible private scratch-tree default are gone.
