# C++ tier changelog

The C++ tier has its own prerelease line because its surface and measured
coverage advance independently from the Python tier.

## [Unreleased]

## [0.1.28] — 2026-10-23

### Added

- Rung-3 metadata gates for `CXXRewrittenBinaryOperator`, `CXXNoexceptExpr`,
  `CXXTypeidExpr` and `CXXFoldExpr`, each checked at an exact retained AST
  path; expression execution remains bounded.

### Measured

- The checked-in corpus now contains 152 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 152 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.27] — 2026-10-23

### Added

- Rung-8 metadata gate for `CXXOperatorCallExpr`, checked at an exact
  retained AST path; overload and conversion execution remain loud.

### Measured

- The checked-in corpus now contains 147 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 147 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.26] — 2026-10-23

### Added

- Rung-7 metadata gates for `CXXConstructExpr`, `CXXBaseSpecifier`,
  `MemberExpr` and `CXXMemberCallExpr`, all checked at exact retained AST
  paths.

### Measured

- The checked-in corpus now contains 146 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 146 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.25] — 2026-10-23

### Added

- Rung-4 metadata gates for `GotoStmt` and `LabelStmt`, a range-loop gate for
  `CXXForRangeStmt`, and rung-10 exception metadata gates for `CXXTryStmt` and
  `CXXCatchStmt`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 141 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 141 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.24] — 2026-10-23

### Added

- Rung-4 metadata gates for `DeclStmt`, `BreakStmt`, `ContinueStmt`,
  `NullStmt`, `CaseStmt`, `DefaultStmt` and `DoStmt`, all checked at exact
  retained AST paths.

### Measured

- The checked-in corpus now contains 136 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 136 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.23] — 2026-10-23

### Added

- Rung-4 metadata gates for `ReturnStmt`, `IfStmt`, `WhileStmt`, `ForStmt`
  and `SwitchStmt`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 129 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 129 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.22] — 2026-10-23

### Added

- Rung-3 metadata gates for `CallExpr`, `CompoundAssignOperator`, `LambdaExpr`
  and `ArraySubscriptExpr`, plus the rung-4 `CompoundStmt` gate, all checked
  at exact retained AST paths.

### Measured

- The checked-in corpus now contains 124 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 124 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.21] — 2026-10-23

### Added

- Rung-2 metadata for `IntegerLiteral` and rung-3 metadata for `DeclRefExpr`,
  `CXXThisExpr`, `UnaryOperator`, `BinaryOperator` and `ConditionalOperator`,
  all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 119 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 119 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.20] — 2026-10-23

### Added

- Rung-2 metadata gates for `CXXBoolLiteralExpr`,
  `CXXNullPtrLiteralExpr`, `CharacterLiteral` and `FloatingLiteral`, all
  checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 112 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 112 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.19] — 2026-10-23

### Added

- Rung-2 metadata gates for `ConstantExpr`, `CXXStaticCastExpr`,
  `CXXConstCastExpr` and `CXXReinterpretCastExpr`, plus the rung-7
  `CXXDynamicCastExpr` gate, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 108 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 108 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.18] — 2026-10-23

### Added

- Rung-1 metadata gates for `InitListExpr`, `CXXParenListInitExpr`,
  `ImplicitValueInitExpr`, `ImplicitCastExpr` and `ParenExpr`, all checked at
  exact retained AST paths.

### Measured

- The checked-in corpus now contains 103 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 103 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.17] — 2026-10-23

### Added

- Rung-1 metadata gates for `CXXTemporaryObjectExpr`, `CXXNewExpr`,
  `CXXDeleteExpr`, `CXXDefaultInitExpr` and `CXXScalarValueInitExpr`, all
  checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 98 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 98 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.16] — 2026-10-23

### Added

- Rung-0 and rung-1 metadata gates for `UsingEnumDecl`,
  `LifetimeExtendedTemporaryDecl`, `MaterializeTemporaryExpr`,
  `CXXBindTemporaryExpr` and `ExprWithCleanups`, all checked at exact
  retained AST paths.

### Measured

- The checked-in corpus now contains 93 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 93 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.15] — 2026-10-23

### Added

- Rung-3 metadata gates for `RequiresExpr`, `TypeRequirement`,
  `SimpleRequirement`, `CompoundRequirement` and `NestedRequirement`, all
  checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 88 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 88 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.14] — 2026-10-22

### Added

- Rung-0 metadata gates for `IndirectFieldDecl`,
  `ClassScopeFunctionSpecializationDecl`, `FriendTemplateDecl`,
  `TemplateParamObjectDecl` and `ImplicitConceptSpecializationDecl`, all
  checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 83 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 83 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.13] — 2026-10-22

### Added

- Rung-0 metadata gates for `ConstructorUsingShadowDecl`, `UsingPackDecl`,
  `UnresolvedUsingTypenameDecl`, `UnresolvedUsingValueDecl`, `BindingDecl` and
  `DecompositionDecl`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 78 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 78 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.12] — 2026-10-22

### Added

- Rung-0 metadata gates for `ClassTemplatePartialSpecializationDecl`,
  `VarTemplatePartialSpecializationDecl`, `ConceptDecl`,
  `CXXDeductionGuideDecl` and `UsingShadowDecl`, all checked at exact retained
  AST paths.

### Measured

- The checked-in corpus now contains 72 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 72 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.11] — 2026-10-22

### Added

- Rung-0 metadata gates for `FunctionTemplateDecl`, `VarTemplateDecl`,
  `TypeAliasTemplateDecl`, `ClassTemplateSpecializationDecl` and
  `VarTemplateSpecializationDecl`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 67 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 67 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.10] — 2026-10-23

### Added

- Rung-0 metadata gates for `FriendDecl`, `TemplateTypeParmDecl`,
  `NonTypeTemplateParmDecl`, `TemplateTemplateParmDecl` and
  `ClassTemplateDecl`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 62 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 62 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.9] — 2026-10-22

### Added

- Rung-0 metadata gates for `CXXMethodDecl`, `EnumConstantDecl`,
  `AccessSpecDecl`, `CXXConstructorDecl`, `CXXDestructorDecl` and
  `CXXConversionDecl`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 57 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 57 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.8] — 2026-10-22

### Added

- Rung-0 metadata gates for `LinkageSpecDecl`, `StaticAssertDecl`,
  `ParmVarDecl`, `CXXRecordDecl` and `FieldDecl`, all checked at exact
  retained AST paths.

### Measured

- The checked-in corpus now contains 51 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 51 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.7] — 2026-10-22

### Added

- Rung-0 metadata gates for `TypedefDecl`, `TypeAliasDecl`,
  `NamespaceAliasDecl`, `UsingDirectiveDecl` and `UsingDecl`, all checked at
  exact retained AST paths.

### Measured

- The checked-in corpus now contains 46 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 46 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.6] — 2026-10-22

### Added

- Rung-0 metadata gates for namespace, function, variable and enum
  declaration occurrences, each checked at an exact retained AST path.
- A rung-5 callable local-reference witness covering mutable and const aliases.

### Measured

- The checked-in corpus now contains 41 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 41 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.5] — 2026-10-22

### Added

- Rung-4 callable witnesses for void returns, forward `goto`/labels, automatic
  local declarations, and nested compound-block scope cleanup.

### Measured

- The checked-in corpus now contains 35 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 35 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.4] — 2026-10-22

### Added

- Rung-4 callable witnesses for `if`, `while`, `do`/`while`, `for`, `break`,
  and `continue`, alongside the existing switch boundary.

### Measured

- The checked-in corpus now contains 30 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 30 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.3] — 2026-10-22

### Added

- Rung-3 callable witnesses for logical `&&`/`||` short circuiting, plain
  assignment, and direct helper calls with integral arguments.
- A rung-4 switch statement witness covering case selection and the default
  arm, plus Boolean statement probes in the differential harness.

### Measured

- The checked-in corpus now contains 24 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 24 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.2] — 2026-10-22

### Added

- Rung-3 callable witnesses for prefix and postfix increment, comma
  sequencing, compound assignment, and conditional branch selection.
- Native differential rows for the admitted callable expression boundaries.

### Measured

- The checked-in corpus now contains 19 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 19 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.1] — 2026-10-22

### Added

- Rung-1 witnesses for vacuous default initialization and its
  uninitialized-read refusal.
- Rung-2 scalar conversion, width and promotion evidence, plus rung-3 defined
  integral expression, unary and shift witnesses with explicit undefined-case
  outcomes.
- Scalar and expression check rows in the differential harness, alongside the
  existing lifecycle and callable rows.

### Measured

- The checked-in corpus now contains 15 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 15 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.0] — 2026-10-22

### Added

- A pinned differential and Clang AST grammar harness, with generated coverage
  and rung-status pages.
- Translation-unit root admission and a rung-1 integral object store covering
  static, thread, automatic, and dynamic storage identities.
- Typed scalar initialization and assignment through borrowed object references,
  including source conversion, shared readback, const-write refusal, and stale
  lifetime/released-storage refusal.
- Kernel-reduced lifecycle witnesses and native C++ probes for the admitted
  boundaries.

### Measured

- The checked-in corpus contains 11 differential rows and 24 grammar witnesses.
  This host has no pinned Clang/LLVM 21.1.8, so the run reports 0 MATCH,
  0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 11 ORACLE rows; grammar reports 24
  ORACLE rows. Missing oracle inputs are kept explicit rather than counted as
  agreement.
