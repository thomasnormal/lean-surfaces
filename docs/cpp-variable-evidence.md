# C++ variable storage and initializer evidence

`LeanModels/Cpp/VariableEvidence.lean` validates a separate, optional supplement
from the pinned Clang/LLVM 21.1.8 canonical probe. It supplies observations
needed by the [automatic-local declaration contract](cpp-local-declarations.md).
It does not admit declarations, allocate objects, execute initializers or
establish lifetime properties. Callable ingestion still refuses `DeclStmt`.

The base wrapper remains `cpp-canonical-probe-0.3`. The supplement has its own
exact API tag, `Clang::VarDecl storage and initializer projection v1`, in
`metadata.variable_evidence_api` and every row's `variable_api`.
`metadata.variable_evidence` contains successful projections;
`metadata.variable_refusals` retains unsupported projections. Old probes still
load as declaration evidence; querying an absent supplement refuses loudly.
A refusal ledger entry is a diagnostic, never a successful evidence row.

## Getter contract

Each successful row contains occurrence, canonical and kind fields, followed
by these mandatory observations. Missing fields are never defaulted.

| Field | Clang getter | Representation |
| --- | --- | --- |
| `local` | `VarDecl::isLocalVarDecl()` | Boolean; includes local static/extern variables, excludes parameters |
| `local_or_parameter` | `VarDecl::isLocalVarDeclOrParm()` | Boolean |
| `storage_class` | `VarDecl::getStorageClass()` | `none`, `extern`, `static`, `private-extern`, `auto`, `register` |
| `storage_duration` | `VarDecl::getStorageDuration()` | `automatic`, `thread`, `static` |
| `tls` | `VarDecl::getTLSKind()` | `none`, `static`, `dynamic` |
| `init_style` | `VarDecl::getInitStyle()` | `c`, `call`, `list`, `paren-list` |
| `has_initializer` | `VarDecl::hasInit()` | Boolean agreeing with the nullable initializer |
| `initializer` | `VarDecl::getInit()` | Explicit null, or the expression projection below |
| `constexpr` | `VarDecl::isConstexpr()` | Boolean |
| `attribute_count` | `Decl::hasAttrs()` / `getAttrs().size()` | Nonnegative integer |

An initializer projection carries its exact occurrence handle and expression
kind, plus `source` and `type` structured type trees.
`source` comes from `getInit()->IgnoreParenImpCasts()->getType()`;
`type` comes from `getInit()->getType()`. These are the same structured
`QualType` vocabulary as the [declaration type supplement](cpp-type-evidence.md),
with witnessed record/enum handles and no parsing of `qualType` text.
The source observation removes parentheses and implicit casts only; it is not
a reconstruction of arbitrary source syntax or an initialization judgment.

Copy-list initialization has style `c` and an `InitListExpr` child. Empty
list initialization has a present `InitListExpr`; it differs from an absent
initializer. Parenthesized aggregate initialization has style `paren-list`
and a `CXXParenListInitExpr`. These distinctions come from Clang, rather than
being inferred from a nonempty list of children. Parameter default arguments
are observations too, including inherited parsed defaults. Unparsed or
uninstantiated defaults are refused before following the initializer pointer.

## Validation and trust boundary

`parseValidatedVariableEvidence` first validates the structured declaration
type supplement. Every variable row must have that type evidence and agree
with every matching declaration-metadata occurrence on kind and canonical
handle. The validator then joins only through the AST root and direct `inner`
array edges. Objects under `referencedDecl`, type fields, arbitrary payloads,
or nested arrays cannot witness a variable occurrence. All matching AST
occurrences must agree; a convenient first stub cannot hide a conflicting row.

Lean checks the raw storage class, TLS and constexpr fields, attribute count,
initialization style, and exact direct-child initializer identity and kind.
Attributes, `FullComment`, `TemplateArgument` and decomposition `BindingDecl`
children are recognized as ancillary children, not initializer expressions.
A row without an initializer requires no value child and no raw `init` field.
Initializer types must have known record/enum references. Role/storage/TLS
consistency checks pin the three possible ordinary-variable/parameter durations;
implicit parameters retain the getter observation without inferring their
internal storage from the ordinary-local flag. Coherent
repeated rows are accepted; conflicting repeats refuse, including differences
in initializer source or converted type.

The streaming producer observes the same root/`inner` reachability before
publishing rows. Unsupported declaration or initializer types, unwitnessed
type references, pending defaults and out-of-dump occurrences remain in the
refusal ledger. Reachability/type refusals report `dump_visible` and
`projection_supported`; a pending-default refusal reports unsupported
projection without dereferencing the pending expression.

The trusted base remains Clang and the thin probe. These checks reconcile
observations with retained JSON; they do not independently derive Clang's
scope classification or type system, authenticate the producer, validate
arbitrary initializer conversions, or establish defined execution. A
well-formed malicious supplement can still lie about facts absent from JSON.
Admission must separately restrict storage, types, initialization forms,
attributes and scopes, then execute against an object-backed frame/store.

## Checks

`VariableEvidenceTests.lean` covers required fields, enum vocabulary, nullable
initializers, type prerequisites, canonical/kind mismatches, AST-only joins,
conflicting occurrences, initializer child shape, attributes, constexpr,
source/converted referents and repeated-row consensus. The focused canonical
probe tests cover all four initialization styles, absent versus empty-list
initialization, source/converted types, parameters, TLS/storage, qualifiers,
shadowing, attributes and explicit type/default refusals. Real Clang-to-Lean
checks include inherited defaults, variable-template specializations and
structured bindings. The existing 18-form declaration battery additionally
validates this supplement while preserving every `DeclStmt` refusal; its
self-initialization control is parsed but never executed as a defined oracle.

```sh
lake build LeanModels.Cpp.VariableEvidenceTests LeanModels.Cpp.Tests
python3 extractors/cpp/test_dump_reachability.py
# With the matching frontend and plugin selected as documented in the extractor README:
python3 extractors/cpp/test_canonical_probe.py
LEANCPP_TEST_LEAN=1 python3 extractors/cpp/test_evidence_ingestion.py
```

This is tool-strength validation, not a new executable rung or a three-corpus
execution census. It leaves the object-backed local executor and its real
artifact proofs as separate obligations.
