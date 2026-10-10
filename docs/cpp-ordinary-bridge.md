# Ordinary C++ declarations — proposed ISO/frontend bridge

2026-10-10. **Specification only. No semantic or runtime admission.**
This refines the [declaration contract](cpp-declarations.md), using the
[schema-0.2 probe](cpp-declaration-pricing.md) as evidence to price a first
implementation. The probe is not an admitted supplement, its pricing results
are not semantic answers, and `LeanModels/Cpp/Translation.lean` still refuses
every execution. No compiler-conformance or program-correctness theorem is
claimed.

## Sources and initial profile

The normative baseline is the charter's C++23 profile, read through WG21
[N4950](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2023/n4950.pdf).
The frontend bridge is pinned to **Clang/LLVM 21.1.8**, not current-development
APIs. Primary implementation sources at `llvmorg-21.1.8` are
[Decl.h](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/clang/include/clang/AST/Decl.h),
[Decl.cpp](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/clang/lib/AST/Decl.cpp),
[DeclBase.h](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/clang/include/clang/AST/DeclBase.h),
[DeclBase.cpp](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/clang/lib/AST/DeclBase.cpp),
[Redeclarable.h](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/clang/include/clang/AST/Redeclarable.h)
and [Linkage.h](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/clang/include/clang/Basic/Linkage.h).
Downloaded headers match the pinned installed headers; external receipts retain
full hashes and commands. N4950 PDF SHA-256 is
`2a2fdee7eb4271263451468ff689d6fd3bbb377d7c6e45375796badfb60d50a2`.

The proposed first profile covers explicitly written, identifier-named,
nonmember **FunctionDecl and VarDecl** declarations in one successfully checked,
complete, nonmodule TU. Only the actual TU and named, non-inline, nonanonymous
namespaces serve as scope infrastructure. Namespace declarations are not
ordinary function/variable definition queries. Tags remain raw evidence only.

Required exclusions are implicit/generated declarations; dependent contexts;
template patterns, specializations, described templates and template ancestry;
modules/header units; class/block/function/template-parameter scopes; friends;
using/alias/decomposition families; unsupported attributes/extensions; and
skipped, pending or otherwise unrepresented definition forms. The source-form
evidence must establish these exclusions, not infer them from a missing field.
Qualified namespace declarations may have different lexical and target scopes.

Linkage-specification-associated declarations and inherited C linkage are
outside the initial entity profile. This includes relevant function-type
origins, not just the immediately enclosing AST node. Merely observing the
declaration language-linkage string `C++` does not establish this exclusion.
Named inline namespaces are excluded conservatively, not classified as non-C++
or flattened into their
parents. These restrictions are general and never depend on a consumer name.

## Four bridges, four different answers

Each bridge is a **named trusted-frontend assumption restricted to this
profile**, plus separately checked artifact facts. Checking JSON graph edges
does not prove Clang implements the standard. The assumptions are part of the
trusted boundary; they must not be introduced as new Lean axioms.

| Query | ISO obligation | Restricted frontend bridge and checked evidence |
| --- | --- | --- |
| Target scope | §6.4.1 `[basic.scope.scope]` p1–2 | Interpret the semantic DeclContext chain as the target scope only for admitted ordinary declarations and TU/named-namespace contexts. Witness every edge, normalize namespace reopening representatives, retain the lexical chain separately, and terminate at the artifact's actual TU. |
| Entity relation | §6.4.1 p4; §6.6 `[basic.link]` p8 | Trust Clang's checked correspondence/type resolution and canonical redeclaration grouping for the admitted families. Validate same-family canonical roots, idempotence, predecessor closure, normalized target scopes and all relevant redeclarations' profile evidence. No grouping by name or `qualType` text. |
| Local definition | §6.2 `[basic.def]` p1–2; §9.5.1 `[dcl.fct.def.general]` p1 | Trust the family-specific declaration-local getter only after the source form and unsupported predicate branches are accounted for. Preserve the original API value alongside the semantic classification. This query need not certify a closed entity group or callable body. |
| Name linkage | §6.6 p2–7 | Trust the formal-linkage API's agreement with the admitted namespace-name rules, after checking the declaration category, scope, source qualifiers/storage and relevant prior declarations. Preserve compiler-internal linkage and the declared name's language linkage separately. |

For ordinary corresponding declarations in the same nonfunction,
nontemplate-parameter target scope and the same TU, §6.6p8 supplies a same-entity
rule. **External linkage is not a prerequisite for that rule.** Type aliases
can give corresponding parameter types with different spellings; overloads can
have identical names in the same namespace and still denote different entities.

`getCanonicalDecl()` is a first-declaration API for these families, not a
persistent entity identifier. A positive or negative entity answer requires
both queried groups' relevant declarations to satisfy the admitted bridge.
Distinct roots justify a negative answer only under that checked, closed
profile and the correspondence assumption. A missing edge, omitted root or
unsupported group produces refusal, never a negative entity answer. No
cross-TU identity, complete ODR compliance, exhaustive definition inventory or
callable-body selection follows from this bridge.

`getDeclContext()` and `getLexicalDeclContext()` are not general ISO scope
getters. Transparent contexts include LinkageSpecDecl; the existing probe does
not emit `getNonTransparentContext()` or `getRedeclContext()`. Arbitrarily
stripping such nodes is not an admitted normalization. Namespace reopening
canonicalization preserves namespace ancestry and flags, not just its spelling.

## Definition and linkage rules to encode

§6.2p2 classifies a definition per declared entity and lists twenty exceptions.
The ordinary subset must implement its applicable exceptions rather than
replace that list with a generic body/completeness bit. Unsupported declaration
families stay refused; the full exception inventory remains in the external
standard review.

- For FunctionDecl, use `FunctionDecl.isThisDeclarationADefinition`, with an
  explicit source-body form and the applicable getter branches witnessed.
  Compound and function-try bodies, defaulting and deletion are distinct forms.
  Deleted/defaulted status is not executable-body availability. The current
  body/defaulted/deleted flags do not cover skipped bodies, pending bodies or
  defining attributes, so unknown cases cannot pass the bridge.
- For ordinary namespace VarDecl, retain
  `VarDecl.isThisDeclarationADefinition` and its exact enum. Under the checked
  profile and getter-to-§6.2 assumption, **0 DeclarationOnly means this
  declaration does not define the variable; 2 Definition means it does**.
  **1 TentativeDefinition refuses**: it has no initial C++23 interpretation.
  Do not Boolean-coerce the enum or query `hasDefinition` instead. Initialized
  extern declarations define; uninitialized ordinary extern declarations do
  not. Demoted definitions, static members, defining attributes, SelectAny and
  template-specialization branches must be excluded or separately established.
- Tag completeness is not this definition query. An opaque enum is excluded
  from definitions by §6.2p2.6 but its type is complete under §9.7.1p3.
  `TagDecl.isThisDeclarationADefinition` is a completion-definition predicate;
  neither an accepted `sizeof` nor type completeness changes its local answer.

For the first name-linkage mapping, require the observed compiler-internal and
formal linkage to agree on `Internal` or `External`, and establish the relevant
§6.6 rule. Namespace `static`, nonvolatile const variables and their extern,
inline or prior-declaration exceptions cannot be inferred from absence of
`storageClass`. Keep `Invalid`, `None`, `UniqueExternal`, `VisibleNone` and
`Module` as named refusals in this initial mapping. This deliberately refuses
some meaningful compiler classifications rather than inventing ISO categories.

Clang's internal enum has Invalid=0, None=1, Internal=2, UniqueExternal=3,
VisibleNone=4, Module=5 and External=6. Its formal projection maps
UniqueExternal to External and VisibleNone to None; enum ordinals are not ISO
linkage values. The current probe emits strings, not these integers. No schema
change or interpretation follows merely from enumerating the APIs.

The separate LanguageLinkage enum has C=0, C++=1 and None=2. For the probed
function/variable **name**, `getLanguageLinkage()` returns None when formal name
linkage is not external. This does not mean no name linkage, nor does it
describe every function type. §9.11 `[dcl.link]` p1 gives function types language
linkage even when a function name has internal linkage. Clang's name query is
not evidence that all C/C++ function-type distinctions are implemented.

The initial bridge cannot be widened to C linkage by adding one enum case:
§9.11p5 introduces no new scope, p6 inherits linkage, and p7 has additional
cross-namespace entity rules. Under §6.2p2.2 and §9.11p8, unbraced
`extern "C" int value;` is nondefining, while `extern "C" { int value; }`
defines the variable.
These are required future counterexamples, not admitted initial forms.

## Proposed evidence and validator contract

No new metadata format is accepted by this item. A future versioned supplement
must retain, rather than silently upgrade, the following distinctions:

| Data | Required representation |
| --- | --- |
| Provenance | Artifact/source/dependency hashes, complete checked frontend invocation and profile, and exact compiler/header/plugin/source versions. Metadata and raw AST must come from the same witnessed process; addresses are artifact-local. |
| Occurrence | Artifact identity plus structural path, including repeated and skeletal occurrences. Rich occurrence witnesses must agree with the consumed metadata family. |
| Frontend node | Artifact identity plus opaque handle, all matching rows and occurrences, explicit null/false/zero fields, and query-local consensus. No first/last representative. |
| Scope | Witnessed semantic and lexical edges, namespace canonical roots/flags/parents and the real TU root. Unsupported/transparent contexts and friend/source-form associations remain explicit. |
| Entity | Admitted canonical representative and relevant redeclaration membership/closure evidence. Resolved correspondence is a frontend assumption, never a string comparison. |
| Local facts | Versioned API tags/domains; own template status; module/dependence/implicit status; source declaration/body/storage/initializer/qualifier/inline facts; excluded attribute/definition branches; linkage specifications, inherited linkage and relevant function-type origins where needed. |
| Query result | Either a typed answer with its clause/profile, assumptions and exact consumed witnesses, or a sorted named refusal set. Unknown is not false, no linkage, declaration-only or a fresh entity. |

The validator operates on immutable literal data, with structurally recursive,
kernel-reducible semantic checks. It must not cache answers or consult source
files during proof reduction. Ingestion may use IO, but must strictly reject
duplicate JSON fields, invalid domains and noninteger numeric tokens **before**
lossy conversion. The existing `Lean.Json`/`rawOfJson` artifact loader is not a
certificate of those new protocol properties. Missing profile/source-form facts
refuse; they are not defaults supplied by a permissive loader.

Checks remain query-local: only required graph closure and facts are consumed;
unrelated raw omissions do not invalidate every query. Conversely, local
definition/linkage telemetry cannot certify entity closure. Keep named
failures for malformed provenance, unwitnessed occurrences, relevant metadata
conflicts, required dangling/cyclic edges, unsupported families/contexts,
unestablished source forms, template/module/linkage exclusions, incompatible
definition enum and an unimplemented bridge. The current pricing tool retains
`semantic-validator-not-implemented` and
`variable-definition-rule-unestablished` unchanged.

## Measured price and acceptance boundary

A bounded read-only pass reused the existing schema-0.2 probes without fresh
extraction or full-AST fingerprint rescans. This is a **candidate slice**, not a
forecast of semantic admission:

| Tooling slice, including library declarations | TinyXML2 | nlohmann/json |
| --- | ---: | ---: |
| FunctionDecl passing canonical + contexts | 3 | 315 |
| VarDecl passing canonical + contexts | 18 | 166 |
| Functions after named/non-inline/nonanonymous namespace, identifier and positive C++ name-language filters | 1 | 232 |
| Variables after those filters | 3 | 151 |
| Namespace scope-infrastructure candidates after those filters | 12 | 179 |
| Semantic queries / runtime functions admitted | 0 / 0 | 0 / 0 |

The positive C++ filter is narrower than the proposed ordinary rule: it drops
internal names reporting None, not just C-linkage names. TinyXML2's sole
function candidate is the included-library `__is_constant_evaluated`, not an
application admission. The slice does not reconstruct source ownership or
reachability, check all missing source-form facts, or establish the ISO bridge.
The previous all-four tooling intersections 26/616 are different populations.
Mox remains strict-refused on its four recorded extension diagnostics, with no
edits or new execution.

The measured pass took 0.636 s / 97,412 KiB RSS for XML and 73.816 s /
3,923,136 KiB for json; input/tool hashes match before and after. The unchanged
source declaration/body/declaration-only census remains XML 205/202/3 and json
1,572/963/609. These are syntax observations, not definition or runtime counts.

Two additional strict compiler probes of a small external diagnostic fixture
took 0.037131/0.036980 s, 91,136 KiB RSS and 73,511 bytes each. Complete
occurrence-path projections of the four relationships and both AST comparison
projections agree across processes, with no missing/unrecognized pointer
witnesses. The observations include namespace reopening, distinct overloads,
qualified namespace definitions, deleted definitions without bodies, opaque
enum completeness, extern initializer/braces distinctions and cross-namespace
C canonical groups. They validate tooling counterexamples, not program
correctness; no prototype theorem is added.

A third strict diagnostic probe took 0.032780 s / 87,668 KiB RSS with no
diagnostics. A function declared through a typedef originating in an extern-C
specification still reports C++ language linkage for its name and TU contexts;
an internal variant reports Internal/None. A later redeclaration of a friend
can also have both contexts at the TU. These observations motivate the missing
type-origin and whole-group association evidence. Predecessor ancestry alone
does not certify that later redeclarations have been covered.

Before implementation admission, extend the versioned evidence for the missing
profile facts, validate strict ingestion and typed literal embedding, and test
each query's rule/refusal separately. Repeat-process alignment and queries over
the unchanged real corpora must cover the existing reopening, out-of-class,
overload, injected-name and template cases; unsupported ones remain explicit
refusals. Any later callable selection and runtime tier require their own
standard contract and compiled-execution oracle.

Receipts: `state/ls-cpp/ordinary-bridge-20261010/{standard,clang,corpus}` retains
exact standard/API citations, source hashes, compiler commands, full projected
relationships, candidate matrices and resource bounds. Raw retention,
cross-TU/ODR refusal and the executable refusal boundary remain unchanged.
