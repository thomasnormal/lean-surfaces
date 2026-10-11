# Structured C++ type evidence

`LeanModels/Cpp/TypeEvidence.lean` is the validation boundary for a future
Clang type projection. It deliberately does **not** parse `qualType` spelling.
The payload is a recursive, structured tree whose nodes are builtin integer
types, pointers, references, cv-qualification, function prototypes, records
and enumerations. Record and enumeration nodes carry frontend declaration
handles, so the type graph remains tied to witnessed declaration occurrences.

Each row carries an occurrence handle, its canonical handle, an explicit
projection API tag, and the structured type tree. `validateTypeEvidence`
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

This is a typed-ingestion validator, not yet a frontend producer or program
interpreter. Existing canonical declaration metadata remains schema-0.3 and
unchanged. A later Clang supplement must emit the exact structured contract,
align rows by occurrence witnesses, and compare independent fresh frontend
runs before any operand or callable-body admission. Until then, no real
source type is treated as admitted by these synthetic guards.

```sh
lake build LeanModels.Cpp.TypeEvidenceTests
```

The guards cover builtin identity, nested pointer/reference/qualification,
function parameters and variadic state, repeated-row consensus, canonical
mismatches, missing occurrences, missing record referents, text-only refusal,
and conflicting type trees.
