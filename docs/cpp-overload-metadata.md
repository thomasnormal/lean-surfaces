# C++ overload and operator metadata

The rung-8 boundary retains Clang's selected overload identity without
performing overload resolution in Lean. `admitResolvedCXXOperatorCallExpression`
requires a `CXXOperatorCallExpr` at the supplied AST path, follows its direct
callee through one-child `ImplicitCastExpr` wrappers, and returns the retained
`FunctionDecl` or `CXXMethodDecl` handle from the callee's `referencedDecl`.

The operation does not use the operator's printed name to select a declaration,
does not infer conversions, and does not execute the selected body. Missing or
non-callable handles refuse. The existing kind-only metadata gate remains for
grammar census rows; this handle-producing gate is the source-shaped identity
boundary for later overload work.
