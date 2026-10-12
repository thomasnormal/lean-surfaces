# Typed source-local callable functions

2026-10-12. `LeanModels/Cpp/Callable.lean` extends the first **callable body
admission** above the source-local declaration rule. It is intentionally a
small, typed C++23 profile; it is not a C++ execution engine. A function is
admitted only when its declaration, direct parameters, structured function type
and retained body all agree in the same Clang probe.

## Admitted profile

The candidate must be a named, ordinary `FunctionDecl` accepted by
`admitLocalFunctionDeclaration` with a direct `CompoundStmt` body. Prototypes,
deleted declarations and function-try bodies remain loud refusals. The body
is represented as a sequence of admitted expression statements, `if`
statements with an optional else branch, `while`/`do` loops, and return
statements. Empty compound and null statements are `skip`. `for` loops,
declarations, assignments, calls, overloaded operations, exceptions, local
functions and every other statement form refuse rather than being silently
represented as a callable.

The function type comes from the validated `Clang::QualType structured type
projection v1` row for the exact occurrence. This slice requires a non-variadic
signature whose result and every parameter are builtin integral types.
Every direct `ParmVarDecl` must have a matching type-evidence row, and its type
must agree, in order, with the function type's parameter list. The result type
is retained as structured `CppTypeEvidence`; no `qualType` string is used to
decide the function signature.

The return-expression profile is:

- a nonnegative decimal `IntegerLiteral` returning exact builtin `int`;
- a parameter `DeclRefExpr`, through only `LValueToRValue` or `NoOp`
  `ImplicitCastExpr` wrappers; or
- an integral `ImplicitCastExpr` (`IntegralToBoolean` or `IntegralCast`) over
  an admitted operand, with a builtin integral destination; or
- a unary integral `+`, `-`, `~` or `!` expression over an admitted operand; or
- a logical `&&` or `||` expression whose operands are builtin integral values
  and whose result is builtin `bool`; or
- an integral `BinaryOperator` whose ordered children, operator and result are
  witnessed by the validated expression supplement and whose promotions agree
  with the explicit `TargetProfile`.

Conditions additionally retain Clang's `IntegralToBoolean` wrapper and evaluate
its builtin boolean result as the condition value.

The result type of the expression must equal the function result type. A
parameter reference must resolve to one of the function's own parameter
handles. Missing rows, mismatched handles, changed child order, unsupported
casts, non-integral operators and conflicting evidence all refuse.

The admitted value is a `CallableFunction` containing a structured signature,
parameter handles/types and a small `CallableStatement` tree. Every typed
expression node retains its source and converted `CppTypeEvidence`; binary
children therefore preserve the promotion witness that admitted them instead
of reducing it to validation-only metadata. It is not a name-based lookup and
does not infer a C++ entity across redeclarations or translation units.

## Trust boundary and nonclaims

The trusted frontend bridge is Clang/LLVM 21.1.8's typed AST and the pinned
canonical probe, together with strict JSON ingestion. Lean checks that every
used occurrence and relationship is present in the same AST and that the
structured type/expression supplements agree with it. The bridge does not
prove Clang's conformance to N4950, overload resolution, implicit conversion
semantics, object lifetime, linkage/ODR, or body completeness outside this
profile.

`LeanModels/Cpp/Translation.execute` remains unconditionally refused. The
callable tree is input to the bounded statement evaluator described in
`docs/cpp-callable-evaluation.md`; admission alone is not a runtime verdict.
In particular, no theorem or differential result may claim that an admitted
body was executed merely because Clang accepted its source.

## Validation

`LeanModels/Cpp/CallableTests.lean` covers identity, literal, typed integral
binary and logical returns, captured `if`/`while`/`do` branches, mismatched evidence,
control-flow and function-try refusals. `extractors/cpp/test_evidence_ingestion.py` has an opt-in pinned
Clang check for real identity/add bodies and a branch admission; it requires the
same explicit compiler/plugin variables as the existing probe tests and skips
otherwise. The evaluator now includes only the profile-checked integral conversion
at its call boundary; broader conversion rules and statements still require their
own semantic models, and `Translation.execute` remains refused.
