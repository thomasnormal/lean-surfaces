# C++ translation artifacts — `cpp-0.1`

2026-10-09. First admission within charter rung 0, indexed to N4950
§5.1–5.2 `[lex.separate]`, `[lex.phases]` and §6.2–6.6
`[basic.def]` through `[basic.link]`. Namespace metadata additionally
belongs to §9.8.2 `[namespace.def]`.

## What is implemented

`extractors/cpp/extract.py` invokes Clang in strict C++23 mode, checks its
exit status, and retains **the entire admitted JSON AST**, including unknown nodes.
There is no C-AST lowering, implicit-conversion stripping, library substitution,
or name-based call dispatch. Compiler rejection is extraction failure, even
when Clang printed a partial AST. Modules, PCH, response files, plugins,
VFS overlays, alternate editions and unlisted driver flags are refused.
Implicit driver configuration is disabled with `--no-default-config`, and
`CCC_OVERRIDE_OPTIONS`/`CCC_ADD_ARGS` are refused rather than allowing hidden
driver controls to override the declared profile.
Forced `-include` headers are sent directly to cc1 as textual includes. This
prevents the driver's automatic use of adjacent PCH/GCH files, which can omit
declarations from the dump and are not admitted translation inputs.

An envelope records `schema_version`, `language`, `edition`, `profile_id`,
absolute `source_file`, `source_sha256`, `frontend`, `dependencies` and `ast`.
The frontend record includes the driver path/hash/full version, target, exact
AST command, cwd, preprocessing environment, predefined macros and diagnostics.
`SOURCE_DATE_EPOCH` is an explicit recorded input, defaulting to zero, rather
than silently using today's date. `-M`/`-MD` captures **system headers too**;
source/header and compiler hashes are checked before and after extraction.
Make dependency paths are tokenized as Make syntax, not shell syntax; quotes
remain literal. Output paths resolving or hard-linked to any manifested input
are refused before creating the temporary output file.
The dependency manifest covers positive file inputs, **not negative
`__has_include` probes or a hermetic filesystem snapshot**. Replaying under a
changed include-search filesystem must re-extract; hashes alone do not certify
replay. Absolute/logical paths are also retained in the AST and driver flags.

`LeanModels/Cpp/{Ast,Json,Load}.lean` checks the schema/profile/edition and
source-manifest consistency, then `load_cpp_artifact` emits a **literal**
`Artifact` term. `Raw` preserves every admitted JSON value: integer values are
recorded exactly as decimal strings, arrays retain order, and object key order
is not semantic. Fractional/exponent numeric tokens (including integral-valued
ones), NaN and Infinity are loudly refused by the extractor, never rounded or
silently changed to JSON strings. Numeric spelling is not a replay guarantee.
Dependency paths must be unique and frontend environment values must be strings.
The parser runs at ingestion; the resulting AST is data, not a call to a
parser. The trust boundary remains Clang plus extraction/ingestion, not Lean
verification of preprocessing or C++ well-formedness. No third-party sources
or machine-specific envelopes are checked into this repository.

The first executable rung-0 gates are `admitTranslationUnit`,
`admitNamespaceDeclaration`, `admitFunctionDeclaration`,
`admitParameterDeclaration`,
`admitRecordDeclaration`, `admitBaseSpecifier`, `admitFieldDeclaration`, `admitMethodDeclaration`,
`admitEnumConstantDeclaration`, `admitAccessSpecification`,
`admitConstructorDeclaration`, `admitDestructorDeclaration`, `admitConversionDeclaration`,
`admitFriendDeclaration`, `admitTemplateTypeParameter`, `admitNonTypeTemplateParameter`,
`admitTemplateTemplateParameter`, `admitClassTemplateDeclaration`, `admitFunctionTemplateDeclaration`,
`admitVariableTemplateDeclaration`,
`admitTypeAliasTemplateDeclaration`,
`admitClassTemplateSpecializationDeclaration`,
`admitVariableTemplateSpecializationDeclaration`,
`admitClassTemplatePartialSpecializationDeclaration`,
`admitVariableTemplatePartialSpecializationDeclaration`,
`admitConceptDeclaration`,
`admitDeductionGuideDeclaration`,
`admitUsingShadowDeclaration`,
`admitConstructorUsingShadowDeclaration`,
`admitUsingPackDeclaration`,
`admitUnresolvedUsingTypenameDeclaration`,
`admitUnresolvedUsingValueDeclaration`,
`admitBindingDeclaration`,
`admitDecompositionDeclaration`,
`admitIndirectFieldDeclaration`,
`admitClassScopeFunctionSpecializationDeclaration`,
`admitFriendTemplateDeclaration`,
`admitTemplateParamObjectDeclaration`,
`admitImplicitConceptSpecializationDeclaration`,
`admitRequiresExpression`,
`admitTypeRequirement`, `admitSimpleRequirement`, and
`admitCompoundRequirement`, `admitNestedRequirement`, and
`admitUsingEnumDeclaration`, and `admitLifetimeExtendedTemporaryDeclaration`,
`admitMaterializeTemporaryExpression`,
`admitCXXBindTemporaryExpression`,
`admitExpressionWithCleanups`,
`admitCXXTemporaryObjectExpression`,
`admitCXXConstructExpression`,
`admitCXXNewExpression`,
`admitCXXDeleteExpression`,
`admitCXXDefaultInitExpression`,
`admitCXXScalarValueInitExpression`,
`admitInitializerListExpression`,
`admitCXXParenListInitExpression`,
`admitImplicitValueInitExpression`,
`admitImplicitCastExpression`,
`admitParenthesizedExpression`,
`admitConstantExpression`,
`admitCXXStaticCastExpression`,
`admitCXXConstCastExpression`,
`admitCXXReinterpretCastExpression`,
`admitCXXDynamicCastExpression`,
`admitCXXBoolLiteralExpression`,
`admitCXXNullPtrLiteralExpression`,
`admitCharacterLiteralExpression`,
`admitFloatingLiteralExpression`,
`admitStringLiteralExpression`,
`admitIntegerLiteralExpression`,
`admitDeclarationReferenceExpression`,
`admitCXXThisExpression`,
`admitUnaryOperatorExpression`,
`admitBinaryOperatorExpression`,
`admitCXXRewrittenBinaryOperatorExpression`,
`admitCXXNoexceptExpression`,
`admitCXXTypeidExpression`,
`admitCXXFoldExpression`,
`admitCXXCoawaitExpression`,
`admitCStyleCastExpression`,
`admitUnaryExprOrTypeTraitExpression`,
`admitVAArgExpression`,
`admitCXXDependentScopeMemberExpression`,
`admitCXXDefaultArgumentExpression`,
`admitCXXUnresolvedConstructExpression`,
`admitUnresolvedLookupExpression`,
`admitCXXPseudoDestructorExpression`,
`admitCXXUnresolvedMemberExpression`,
`admitCXXDependentScopeDeclRefExpression`,
`admitCXXInheritedConstructorInitExpression`,
`admitCXXStdInitializerListExpression`,
`admitCoroutineBodyStatement`,
`admitAttributedStatement`,
`admitDesignatedInitializerExpression`,
`admitCoreturnStatement`,
`admitIndirectGotoStatement`,
`admitCapturedStatement`,
`admitOMPParallelDirective`,
`admitOMPForDirective`,
`admitOMPForSimdDirective`,
`admitOMPSectionsDirective`,
`admitOMPSectionDirective`,
`admitOMPSingleDirective`,
`admitOMPMasterDirective`,
`admitOMPTaskDirective`,
`admitOMPTaskloopDirective`,
`admitOMPTaskloopSimdDirective`,
`admitOMPTeamsDirective`,
`admitOMPTeamsDistributeDirective`,
`admitOMPTeamsDistributeSimdDirective`,
`admitOMPTeamsDistributeParallelForDirective`,
`admitOMPTeamsDistributeParallelForSimdDirective`,
`admitOMPTargetDirective`,
`admitOMPTargetDataDirective`,
`admitOMPTargetEnterDataDirective`,
`admitOMPTargetExitDataDirective`,
`admitOMPDistributeDirective`,
`admitOMPDistributeParallelForDirective`,
`admitOMPDistributeParallelForSimdDirective`,
`admitOMPDistributeSimdDirective`,
`admitOMPParallelForDirective`,
`admitOMPParallelForSimdDirective`,
`admitOMPParallelSectionsDirective`,
`admitOMPParallelMasterDirective`,
`admitOMPOrderedDirective`,
`admitOMPAtomicDirective`,
`admitOMPFlushDirective`,
`admitOMPBarrierDirective`,
`admitOMPTaskwaitDirective`,
`admitOMPTaskyieldDirective`,
`admitConditionalOperatorExpression`,
`admitCallExpression`,
`admitCompoundAssignmentOperator`,
`admitLambdaExpression`,
`admitArraySubscriptExpression`,
`admitMemberExpression`,
`admitCXXMemberCallExpression`,
`admitCXXOperatorCallExpression`,
`admitCompoundStatement`,
`admitReturnStatement`,
`admitIfStatement`,
`admitWhileStatement`,
`admitDoStatement`,
`admitForStatement`,
`admitRangeForStatement`,
`admitSwitchStatement`,
`admitCaseStatement`,
`admitDefaultStatement`,
`admitDeclarationStatement`,
`admitBreakStatement`,
`admitContinueStatement`,
`admitNullStatement`,
`admitGotoStatement`,
`admitLabelStatement`,
`admitLabelDeclaration`,
`admitCXXTryStatement`,
`admitCXXCatchStatement`,
`admitCXXThrowExpression`,
`admitVariableDeclaration`, `admitEnumDeclaration`,
`admitTypedefDeclaration`, `admitTypeAliasDeclaration`,
`admitNamespaceAliasDeclaration`, `admitUsingDirectiveDeclaration`,
`admitUsingDeclaration`, `admitLinkageSpecification` and
`admitStaticAssertion`. The root gate checks
the retained root's explicit `kind` for `TranslationUnitDecl`; the
namespace gate then checks a nonempty artifact occurrence path and requires
`NamespaceDecl` at that exact path, while each declaration gate applies the
same path check to its corresponding kind. All one hundred sixty-eight return typed metadata results without
inspecting or erasing child nodes,
resolving names, or executing a body. Malformed roots, absent paths and other
node kinds refuse with named diagnostics. `Translation.execute` remains the
loud boundary for declaration execution, including an otherwise empty
function, until object, lifetime, type, expression and statement semantics are
threaded through the artifact.

## Declaration inspection, not declaration semantics

`Artifact.declarations` is a structurally recursive index over AST `inner`
children. It records declaration **occurrences**, including each occurrence's
zero-based path through nested `inner` arrays, original TU-local Clang IDs,
names, types, mangled names, lexical ancestors, semantic-parent and
redeclaration links, and raw location/range fields. Reference stubs outside
`inner` are not new occurrences; repeated IDs inside `inner` are retained as
separate path-bearing occurrences. IDs are compiler-session handles, never
persistent or cross-TU identities.
The root path is `[]`; each subsequent index addresses the original `inner`
array, including non-declaration siblings and intervening statement nodes.
These paths are local to this artifact, not canonical-node or entity identities.
`Artifact.declarationAtPath` is the corresponding occurrence-local lookup;
lookup by a repeated frontend ID remains a list, not an implicit canonical
choice. `Artifact.previousDeclCandidates` applies the same rule to a retained
`previousDecl` handle: it returns every matching occurrence, or `[]` for a
dangling handle, without asserting that any candidate is the same entity.
`Artifact.semanticParentCandidates` does the same for `parentDeclContextId`;
these are raw occurrence candidates, not proven semantic-parent relations.
The unmodified AST additionally retains namespace aliases, original-namespace
links, template arguments, instantiated bodies, value categories, conversions,
cleanups and macro spelling/expansion locations.

The index does **not** infer linkage, merge entities, resolve qualified names,
check ODR/linking, validate context-link graphs, infer missing template bodies,
or expand Clang's elided locations. An omitted location stays omitted, not
an invented source-ownership claim. The next rung-0 obligations are specified
in the [declaration/entity/linkage contract](cpp-declarations.md).
Preserving their inputs is not implementing their rules. Types are compiler
metadata, not semantic type-equality proofs.

`LeanModels/Cpp/Translation.lean` refuses **every execution**, including empty
functions, literal returns, unknown declarations and library calls. Therefore
executable admission, MATCH and DIVERGE counts are zero. This is an artifact
admission step, not completion of rung 0 or a C++ interpreter. No program
correctness theorem or prototype example is claimed.

## Validation

The extractor's focused regression tests compare retained metadata with a
second Clang dump, check system/transitive/forced includes and mutation, and
exercise compiler-error/flag/atomic-output refusals. Temporary compiler probes
test tooling; they are not evidence of C++ execution coverage. Lean guards
check occurrence indexing, overload distinction, parent/redeclaration links,
reference-stub exclusion, repeated-ID paths, non-declaration traversal and
unconditional refusal. An integration test loads a freshly extracted envelope
as a literal Lean term, including opaque data, and compares every declaration
path with an independent traversal of the retained Clang AST.
Run `python3 extractors/cpp/test_extract.py` with Clang available on `PATH`.

Example extraction and inspection commands:

```console
python3 extractors/cpp/extract.py /path/to/original.cpp --out /tmp/original.cpp.json -- -I/path/to/includes
lake build LeanModels.Cpp
python3 extractors/cpp/test_extract.py
```

Each census must separately report source-owned and dependency bodies,
extraction errors, actual execution and refusal walls. Whole-body node sets
are prerequisite telemetry, not claims that dropping one node would admit
execution. Corpora and dated receipts remain external as in the charter.
