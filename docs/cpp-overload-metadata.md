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

The same handle contract is available for ordinary `CallExpr` nodes through
`admitResolvedCallExpression`; direct function and method references retain
their Clang declaration identity while name lookup and invocation remain loud.

`admitResolvedCXXConstructExpression` applies the same contract to
`CXXConstructExpr` only when the AST carries a selected
`CXXConstructorDecl` handle in its structured `ctor` field. The pinned Clang
21.1.8 JSON for an ordinary `S value(1)` construction carries `ctorType` but
no `ctor` handle, so that source shape is recorded as a loud refusal rather
than treating the type spelling as overload identity. Construction,
conversion, and lifetime execution remain outside this metadata gate.

The positive kernel witness and differential row use a structured `ctor`
object with a retained `CXXConstructorDecl` handle. They demonstrate the
accepted evidence shape without claiming that constructor overload resolution
or object construction has been executed.

Ordinary `CallExpr` identity has the corresponding negative control: a
retained declaration handle whose structured kind is `VarDecl` is refused even
when the separate native source witness is well-formed. The gate never turns a
non-callable declaration into a callable by name.

The positive ordinary-call corpus also covers the one-child implicit-cast path,
confirming that the retained function handle survives the frontend wrapper
without string lookup or conversion inference.

A malformed cast wrapper with two children is a recorded refusal; the gate
requires the exact one-child frontend shape and does not choose one child by
position.

An empty `CallExpr` child list is likewise a recorded refusal; a selected
callee cannot be manufactured when the frontend supplies no callee occurrence.
