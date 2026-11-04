# C++ declarations, entities and linkage — rung-0 specification

2026-10-09. **Specification, not implementation or executable admission.**
The [translation-artifact tier](cpp-translation.md) retains the inputs below;
its declaration index does not establish these semantic relationships.
`LeanModels/Cpp/Translation.lean` still refuses every execution.

The [query-local evidence pricing tool](cpp-declaration-pricing.md) measures
witnessed candidates separately for canonical nodes, contexts, local definition
flags and compiler linkage telemetry. It does not implement this semantic
contract; every result retains explicit semantic barriers.
Its versioned own-template API gates are tooling evidence, not an implementation
of ISO template/entity rules or an executable admission.
The [ordinary-declaration bridge](cpp-ordinary-bridge.md) now specifies the
restricted ISO/frontend assumptions, missing evidence and typed-validator
obligations for a first function/variable subset. It is not implemented admission.
`LeanModels/Cpp/Identity.lean` now exposes only a conservative
`canonicalTargetCandidates` bridge: explicit metadata rows must agree on kind
and canonical handle, and the result is every matching artifact occurrence.
Missing/conflicting evidence or an absent target refuses; this remains frontend
evidence, not an entity-identity theorem or executable admission.
The same module exposes `functionDefinitionEvidence` for a `FunctionDecl` only
when all matching rows carry the same parsed local shape; its Boolean is a
frontend observation, not a proof of an ISO definition, callable body or ODR
fact.
`canonicalRootEvidence` adds the bounded root gate: the root must be
same-family and idempotent with an explicit null predecessor, while a nonroot
must carry a predecessor. It still does not follow a complete predecessor
chain or establish an ISO entity.
`canonicalPredecessorChainEvidence` follows that explicit predecessor chain
to the root with a finite artifact-bound fuel and refuses cycles, dangling
targets, inconsistent repeated rows and chains that terminate before the
canonical root. It remains frontend graph evidence, not an entity proof.
`semanticContextChainEvidence` and `lexicalContextChainEvidence` follow a
finite, artifact-backed handle chain to the translation-unit root. Cycles,
missing metadata or artifact targets, nonroot null parents and nonnull
translation-unit parents refuse. The source must match its actual artifact
occurrence, every occurrence of each visited handle must agree with the
metadata's declaration kind, and the terminal translation unit must occur at
the artifact's root path. A nested node labelled as a translation unit cannot
close the chain. Repeated same-kind occurrences are retained, not deduplicated;
the returned chain remains frontend evidence, not validated ISO scope membership.
`semanticContextCandidates` and `lexicalContextCandidates` likewise consume
only explicit metadata handles and return occurrence candidates; null context
is `[]`, while conflicting evidence or an absent target refuses. They do not
assert complete scope chains or ISO scope membership.
`linkageEvidence` similarly retains the pinned compiler internal/formal and
applicable language-linkage enum strings only when repeated rows agree and all
required values are in the admitted vocabulary. It is compiler telemetry, not
an ISO linkage mapping or an entity theorem.

## Standard obligations and trusted boundary

Baseline: the charter's C++23 profile and WG21
[N4950](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2023/n4950.pdf).
Clause references describe obligations, not implemented coverage:

| Clause | Declaration-layer obligation |
| --- | --- |
| §6.2 `[basic.def]` | Distinguish declarations, introduced names/entities and definitions; a declaration can have effects without introducing an entity. |
| §6.3 `[basic.def.odr]` | Distinguish definable items and permitted multiple definitions; a translation-unit graph is not a program-wide ODR certificate. |
| §6.4.1 `[basic.scope.scope]`, §6.5 `[basic.lookup]` | Represent target scopes and declaration correspondence separately from spelling, lexical AST nesting and already-resolved uses. |
| §6.6 `[basic.link]`, particularly paragraphs 2–8 | Separate internal/external/module/no name linkage; corresponding declarations, target scope and TU/module/linkage conditions participate in entity identity. |
| §9.8.2 `[namespace.def]`, §9.8.3 `[namespace.alias]` | Preserve namespace reopenings, unnamed/inline namespaces and namespace aliases without merging by spelling. |
| §9.11 `[dcl.link]` | Keep language linkage distinct from name linkage, including its additional identity rules. |
| §9.5 `[dcl.fct.def]`, §12 `[over]`, §13 `[temp]` | Separate ordinary/defaulted/deleted definitions, overload entities, template patterns and emitted specializations. |

Clang remains trusted for preprocessing, lookup, type checking, overload
selection and instantiated declarations. The model must preserve and validate
the references it consumes, not invent a second name-based resolver. An
independent Clang query is a tooling oracle, not a proof of Clang conformance.
Malformed artifact data is distinct from a source program's language error.

The pinned
[Clang 21.1.8 JSON dumper](https://github.com/llvm/llvm-project/blob/llvmorg-21.1.8/clang/lib/AST/JSONNodeDumper.cpp)
emits declaration IDs from pointers, emits `parentDeclContextId` when lexical
and semantic declaration contexts differ, and supplies original-namespace
references for namespace reopenings. These are profile-specific frontend
facts. They do not make all enclosing `inner` nodes C++ scopes or supply a
complete canonical-declaration graph.

## Three identities, four separate questions

The future semantic layer must keep these notions distinct:

- **Occurrence:** one position in one admitted artifact's structural AST.
  An occurrence witness contains the artifact and its structural path, not
  just a source span or list of ancestor IDs. Repeated emitted positions stay
  distinct even if they repeat a Clang ID.
- **Frontend declaration node:** an artifact-scoped opaque Clang handle.
  Multiple occurrences may describe this same node with different amounts
  of metadata. The handle has no meaning in another compiler invocation.
- **Entity:** a validated semantic grouping of declarations in an explicitly
  admitted family. A redeclaration can have a different frontend handle;
  equality of names or handles alone is not the general entity relation.

Scope membership, entity identity, definition status and callable-body
selection are separate queries. Each requires its own supported evidence.
Name bindings and their targets remain separate: alias/using observations do
not automatically become fresh entities or definitions of the referred target.
Every successful query retains occurrence witnesses and its used evidence;
it must not erase unresolved data elsewhere in the artifact.

An entity query has one of two outcomes: a supported answer with evidence,
or a named refusal. Lack of a graph edge is not evidence that two declarations
denote different entities. In particular, absent `previousDecl` does not
universally establish a first declaration. Unknown is not false, no linkage,
declaration-only, or external linkage.

## Admission contract

Artifact ingestion remains permissive about unknown AST constructs and
unresolved declaration links. Semantic admission is a **separate** operation
on the evidence needed by a requested query, with the following obligations:

1. Resolve handles only within the supplying artifact. Preserve all matching
   occurrences; neither first-wins nor last-wins may discard richer metadata.
   Missing optional fields are unknown unless a supported, versioned emission
   rule establishes their meaning. Conflicting present fields relevant to
   the query produce a diagnostic rather than an arbitrary representative.
   Differing lexical paths alone are not a contradiction.
2. Track the emitted lexical path separately from semantic declaration
   context and target scope. An explicit semantic parent is never overwritten
   with the nearest lexical ancestor. A supported context rule or additional
   frontend evidence is required where the context is omitted.
3. Follow only versioned, declared edge families such as supported
   redeclaration and original-namespace references. Detect required dangling
   targets, cycles, incompatible declaration families and contradictions.
   Preserve a dangling edge as unresolved evidence; refuse a query that
   needs it, without invalidating unrelated raw artifact inspection.
4. Establish entity grouping through an admitted rule and sufficient
   frontend/context evidence. Neither connected raw pointer strings nor
   canonical-root guesses discharge all C++ identity conditions. A versioned
   Clang-tooling supplement may report canonical declarations and semantic
   classifications, but joins must identify exact occurrences and all added
   trusted computations must be documented. No such supplement is admitted.
5. Check resolved uses against supported targets. Equal spellings, mangled
   names, `qualType` strings, header hashes and source coordinates cannot
   replace declaration correspondence, semantic type relationships or
   resolved overload references. An unresolved/dependent use refuses its
   semantic query; a call is never dispatched by first matching name.

The admission result is immutable data, not a runtime cache. These checks
must not depend on traversal order, the identity of a consumer library, or
unrecorded compiler configuration. Any future environment or choice affecting
an answer is an explicit input under the charter's oracle discipline.

## Definitions, linkage and programs

Definition classification is per declaration/entity pair, with an explicit
unknown case. An entity can have both non-defining and defining declarations.
A body-node census does not classify every definition: defaulted and
deleted functions, variable declarations, classes and template declarations
have their own rules. A template pattern's body does not by itself establish
a callable instantiated specialization. Selecting a body does not establish
that its expressions, lifetime effects or statements are executable in-tier.

Name linkage is not storage class, storage duration, language linkage, or
binary visibility. For example, namespace-scope const variables, unnamed
namespaces, prior declarations and class membership affect `[basic.link]`;
absence of `storageClass` cannot mean external linkage. Class-member `static`
must not be treated as namespace-scope `static`. Language linkage needs its
own enclosing specification and function-type evidence. No textual C-AST
storage/default or first-name-match convention is inherited from the C tier.

A future `Program` contract must name its complete set of admitted TUs and
module assumptions before cross-TU entity matching. The same included header
in two TUs supplies two frontend graphs, not automatically one entity. Inline
and templated definitions cannot be rejected merely because several bodies
are observed, nor accepted because their hashes match. ODR requires the
applicable definition, token and name-resolution obligations, among others.
Successful linking is neither a complete ODR diagnostic nor an ODR proof.

For the initial semantic admission subset, modules/header units, unsupported
declaration families, unrepresented linkage rules and unresolved template
dependence remain named refusals. Raw retention continues unchanged.
The separate [source-local function rule](cpp-local-functions.md) implements
only four function declaration forms, not this entity subset or a cross-TU
admission.

## Evidence from original artifacts

The external receipt `ls-cpp-r0-census/declaration-identity-20261009` was
measured over the **unchanged** TinyXML2 `321ea883` source/profile from the
translation census. Its 10,232,056-byte envelope has 4,546 declaration
occurrences but 4,510 distinct Clang IDs. There are 264 `previousDecl` edges,
including one target absent from the index, and 212 explicit semantic-parent
edges whose targets are present. These are raw-AST measurements, not entity
or ownership theorems. Concrete counterexamples to shortcut rules:

- The header and `.cpp` openings of `tinyxml2` have distinct IDs connected by
  `previousDecl` and `originalNamespace` (`tinyxml2.h:114`, `tinyxml2.cpp:138`).
- `XMLDocument::Parse(const char*, size_t)` is declared inside the class
  (`tinyxml2.h:1754`) but defined lexically in the namespace
  (`tinyxml2.cpp:2460`), with an explicit class semantic parent and predecessor.
  The separate `Parse()` overload must not merge through parent/name equality.
- `XMLDocument` has a forward declaration, a complete declaration and an
  implicit injected occurrence; identical spelling/location does not identify
  the redeclaration relation of all three.
- `CreateUnlinkedNode` repeats one ID in a full occurrence and a skeletal
  template occurrence. `INITIAL_SIZE` repeats one parameter ID along eight
  paths. Rejecting all duplicate IDs or taking the last record would mishandle
  real frontend output.
- An external `align_val_t` enumeration has a predecessor absent from the
  declaration index. No reason for its omission is inferred.

The receipt retains full IDs, paths, metadata, hashes and reproducible commands
externally; pointer strings are not stable checked-in fixture expectations.
The json corpus still has an admitted raw artifact, and strict extraction of
the extension-heavy input still fails on the recorded non-standard declarations. Neither has a new
declaration-semantic verdict. Runtime admissions/verdicts remain zero on all
three corpora, behind `rung-0:no-executable-semantics`.

## Acceptance obligations for implementation

Before admitting any semantic declaration query:

- Census every relevant declaration, context, redeclaration, namespace and
  resolved-reference edge family in both admitted real corpora; report
  duplicates, dangling targets, unknown metadata and unsupported families.
- Compare queried relationships against independent Clang canonical/context,
  linkage and definition queries on those same sources and exact profile.
  Align by witnessed occurrences, never raw pointer equality across runs.
- Repeat extraction with fresh compiler processes: permit new handles while
  requiring the supported semantic relationships to agree after alignment.
- Pin real namespace reopening, out-of-class definitions, overloads,
  injected names and template repetition as artifact-level acceptance cases.
  Mutation fixtures test diagnostic behavior, not program correctness.
- Keep cross-TU symbol observations separate from ODR claims; price and
  specify any added frontend supplement before trusting it. Report semantic
  admission separately from raw extraction and from actual runtime tests.

This specification supplies a measured reason not to implement a name/ID
heuristic. The optional [metadata probe](../extractors/cpp/README.md) is a
separately versioned tooling experiment, not an admitted extractor supplement
or implementation of this contract. The subsequent
[two-corpus pricing](cpp-canonical-evidence.md) now includes completed full-AST
payload projection comparisons while retaining explicit pointer-witness and
declaration-graph refusals; it does not discharge all acceptance obligations.
There is no interpreter,
declaration theorem about a prototype, or silent trust-boundary extension.
