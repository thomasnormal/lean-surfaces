# Structured C++ type evidence

`LeanModels/Cpp/TypeEvidence.lean` is the validation boundary for the
structured type projection emitted by `extractors/cpp/canonical_probe.cpp`.
The plugin queries `clang::QualType` in the same AST context as the declaration
metadata and deliberately does **not** parse `qualType` spelling.
The payload is a recursive, structured tree whose nodes are builtin integer
types, pointers, references, cv-qualification, function prototypes, records
and enumerations. Record and enumeration nodes carry frontend declaration
handles, so the type graph remains tied to witnessed declaration occurrences.

Each row carries an occurrence handle, its canonical handle, an explicit
projection API tag, and the structured type tree. `parseValidatedTypeEvidence`
loads the `metadata.type_evidence` array and `validateTypeEvidence`
requires the occurrence and canonical handles to agree with the existing
declaration metadata, rejects absent record/enum referents, and accepts
repeated occurrences only when their canonical handle and complete type tree
agree. A conflicting repeat is a refusal, not a last-row-wins cache update.

The parser accepts only the following exact node tags: `builtin`, `pointer`,
`lvalue-reference`, `rvalue-reference`, `qualified`, `function`, `record` and
`enumeration`. Builtin names map to `CppIntType` identities; equal widths are
not used as a substitute for those identities. Text-only `{ "qualType": … }`
payloads, unknown builtin names, empty qualifiers, malformed children and
unrepresented type families refuse loudly.

The canonical probe emits rows only when the complete type tree belongs to
this admitted vocabulary; unsupported Clang type families are omitted rather
than guessed from text. Its additive `type_refusals` ledger names typed
declarations rejected for unsupported qualifiers, function properties, missing
witnesses or recursion depth. Existing canonical declaration metadata remains
schema-0.3, with `type_evidence_api`, `type_evidence` and `type_refusals` as an
additive supplement. The output is still tooling evidence: independent fresh
frontend runs must agree by occurrence witnesses before any operand or
callable-body admission, and no program execution is admitted by this item.

The same probe now emits a separate `expression_evidence` supplement for
builtin `BinaryOperator` nodes. Each row carries the AST occurrence handle,
operator spelling, structured result type, and the two ordered direct-child
handles with both their pre-conversion source types and Clang's converted
types. The probe observes the JSON dump as it is emitted from the same
`ASTContext`. Its visitor can see more Clang expression occurrences than
`-ast-dump=json` serializes (for example, an array-bound expression), so an
occurrence absent from that dump is a refusal, not an evidence row. Lean checks
the occurrence kind, opcode, child order and child kinds against the retained
AST, and checks every record or enumeration reference against the declaration
ledger. For builtin integral rows, the explicit `TargetProfile` bridge can
check promotions and usual arithmetic conversion types; this is a type check,
not value evaluation. Unsupported operand or result type families remain in
`expression_refusals`; no `qualType` text is used and no overloaded operator,
conversion or executable expression is admitted by this supplement. The
separate [typed callable bridge](cpp-callable-functions.md) consumes these
rows for its admitted integral bodies; it performs no body execution
and leaves `Translation.execute` refused.

The optional `expression_types_api` supplement has the exact tag
`Clang::Expr type projection v1`. Its `expression_types` array carries each
representable expression's occurrence, AST kind and structured `Expr::getType()`;
`expression_type_refusals` retains unrepresented types and occurrences outside
the dump. This preserves implicit cast destinations independently of a parent
binary operation or function signature. `parseValidatedExpressionTypeEvidence`
joins only the AST root and recursive `inner` children, checks all matching
kinds and referenced declarations, and requires repeated rows to agree.
An absent tag and array mean a legacy capture; either alone, an unknown tag,
or conflicting rows refuse. A present-empty array remains a supplied
supplement: a consumer requiring an expression type must refuse a missing row.
The [callable bridge](cpp-callable-functions.md#expression-type-preservation)
uses this supplement without changing the schema-0.3 wrapper or raw AST.

## Fresh capture validation

On 2026-10-19 a fresh pinned capture using Clang/LLVM 21.1.8 produced a
16,199-byte probe whose SHA-256 is
`ba01101e6aa903ffa7e07bb4db669cd7696b79984e94b0d68e4920a42e76d86d`.
The capture receipt binds that payload digest and the probe contains ten
declaration rows; the same-process inspection accepts its four type rows and
reports zero expression rows for the declaration-only control. The focused
capture suite passes **48 tests / 0 failed** with the declared 16 GiB process
bound.

The unchanged full XML-profile probe remains a negative control for the
expression join. Its 34,496,558-byte SHA-256 is
`e8db863c3f2fc3d8aaa44028d243064b7cef0d35ffe1061c9a96efd4f6185d6d`.
Inspection accepts its 2,015 type rows but refuses the expression supplement
with `expression evidence occurrence is absent from AST`; the artifact hash is
unchanged before and after inspection. This preserves the distinction between
a fresh pinned capture and the earlier full-corpus evidence boundary.

```sh
lake build LeanModels.Cpp.TypeEvidenceTests
```

The guards cover builtin identity, nested pointer/reference/qualification,
function parameters and variadic state, repeated-row consensus, canonical
mismatches, missing occurrences, missing record referents, text-only refusal,
and conflicting type trees. The optional Clang probe test additionally checks
real occurrence-witnessed builtin, pointer, reference, cv-qualified, function,
record and enumeration rows without a `qualType` fallback.
