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

```sh
lake build LeanModels.Cpp.TypeEvidenceTests
```

The guards cover builtin identity, nested pointer/reference/qualification,
function parameters and variadic state, repeated-row consensus, canonical
mismatches, missing occurrences, missing record referents, text-only refusal,
and conflicting type trees. The optional Clang probe test additionally checks
real occurrence-witnessed builtin, pointer, reference, cv-qualified, function,
record and enumeration rows without a `qualType` fallback.
