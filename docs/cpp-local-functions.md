# Source-local C++ function declarations

2026-10-10. `LeanModels/Cpp/LocalFunction.lean` admits a first **local
declaration form**, not an entity group, function type or executable function.
The rule follows [C++23 N4950](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2023/n4950.pdf)
§6.2 `[basic.def]` p2.1 and §9.5
`[dcl.fct.def]`: a bodyless ordinary function declaration is nondefining;
a compound body, function-try body or explicitly deleted definition defines
the function. The embedding keeps these four forms distinct, preserves each
body and parameter as literal `Raw`, and computes `definesEntity` from the
form rather than exposing a compiler Boolean as the semantic answer.

## Checked boundary

`admitLocalFunctionDeclaration probe path` addresses an exact occurrence in
the schema-0.3 probe's own AST. No independently supplied artifact is joined.
It checks source/metadata family and name agreement, repeated-row consensus,
the ordinary non-template enum branches and both witnessed context chains.
Lexical ancestry must match the actual AST occurrence; an explicit semantic
parent must match the metadata. Only the actual translation unit and named,
non-inline, nonanonymous namespaces are admitted as context infrastructure.
Namespace reopening is not flattened or converted into an entity identity.

The initial profile excludes implicit declarations, dependent contexts,
modules, templates/specializations, nonidentifier or non-ASCII names,
class/block/function/linkage-specification scopes, attributes, defaulting,
skipped/pending/late-parsed bodies and unknown direct child forms. Parameters
precede at most one terminal compound or function-try body. Deleted forms
must be bodyless. A body must be owned by this declaration, and its AST kind
must agree with the recorded local-body kind. Deletion and definition getters
must agree with the source classification. Missing, malformed or conflicting
required evidence refuses. A body borrowed from a later redeclaration refuses;
a properly witnessed prototype itself remains nondefining.

## Trusted assumption and nonclaims

The restricted frontend bridge is explicitly **Clang/LLVM 21.1.8's checked
source-form and declaration-local getter correspondence to these C++23
rules**, on a successfully checked complete C++23 translation unit. The
schema records getter APIs; it does not prove compiler conformance. The
assumption is documented at the ingestion boundary, not introduced as a Lean
axiom. The direct AST flags are interpreted using this pinned JSON dumper,
not another frontend's omission conventions.

This local rule is independent of the proposed ordinary **entity** profile
in `cpp-ordinary-bridge.md`. It establishes neither that profile's complete
language-linkage/type-origin exclusions nor a name linkage, target-scope
normalization, canonical entity relation, ODR result, full program admission
or capture provenance. Inherited linkage does not change the supported
source-local definition rule; linkage-specification AST contexts are still
conservatively refused. Retained parameter/body JSON is not a typed or
executable embedding. The separate [typed callable slice](cpp-callable-functions.md)
consumes only a stricter direct-return subset of these compound bodies; this
local rule itself still admits no typed callable or execution. `execute` remains
unconditionally refused.

## Validation and corpus inspection

`LocalFunctionTests.lean` exercises each form and contradictory/missing
evidence without adding a prototype correctness theorem. The opt-in pinned
compiler test in `extractors/cpp/test_evidence_ingestion.py` checks prototypes,
compound/try/deleted bodies, qualified namespace definitions and namespace
reopening, plus named refusals for attributes, templates, methods, anonymous
and inline namespaces and linkage specifications. This is a source-form
oracle check, not differential execution of a C++ interpreter.

The existing runtime inspector supports `--local-functions`, counting exact
FunctionDecl occurrences by admitted local form or refusal reason on an
unchanged real probe. These counts never mean callable/runtime functions.
The unchanged TinyXML2 probe has 442 FunctionDecl occurrences: two local
compound definitions admitted, 440 refused, zero runtime functions admitted.
The admitted source occurrences are `TIXML_VSCPRINTF` and `callfopen`, not
synthetic replacements. This does not complete the three-corpus rung: the
larger JSON-library probe still has no successful runtime load and the third
corpus retains its strict frontend refusal.
Other declaration families, variable definition rules, entity admission and
the later interpreter rungs remain unfinished.
