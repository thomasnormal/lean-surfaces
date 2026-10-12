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
statements with an optional else branch, `while`/`do`/bounded `for` loops, loop-local
`break`/`continue`, parameter-targeted
`=`, integral compound assignments, and parameter-targeted prefix/postfix
increment and decrement expressions. Empty compound
and null statements are `skip`. Declarations, local-variable/member assignments,
calls, overloaded operations, exceptions, local functions and every
other statement form refuse rather than being silently represented as a callable.

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
- a prefix or postfix `++`/`--` over a direct non-boolean integral parameter
  reference; or
- a `ConditionalOperator` with a builtin integral condition and two branches
  whose represented types agree; or
- a comma expression whose builtin integral result type is the right operand's
  represented type; or
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
casts, non-integral operators, unsequenced side effects in ordinary binary
operands and
conflicting evidence all refuse. Increment and decrement are not generalized
to locals, members, calls or overloaded operators. Conditional expressions with
an omitted middle operand, unrepresented conversions or mismatched branch
types remain loud refusals.

Comma expressions retain C++'s left-to-right sequencing boundary. Their left
operand must complete successfully before the right operand is evaluated, and
effectful expressions nested beneath either operand are rejected when they
would otherwise be unsequenced inside a binary expression.

The admitted `for` shape has a parameter-only initializer and step, an explicit
integral condition, and an admitted body. It is lowered to the equivalent
state-threaded `while` sequence; condition declarations, omitted conditions,
and loop transfers in the body remain loud refusals. `break` and `continue` are
admitted inside `while` and `do` bodies and remain loud at the public boundary
when no loop consumes them.

The compound-assignment statement profile covers `+=`, `-=`, `*=`, `/=`, `%=`,
`&=`, `|=`, `^=`, `<<=` and `>>=`. Its target must be a direct reference to an
integral parameter. The exact ordered children, operator and structured types
must agree with the binary-expression supplement, including the left child's
parameter type. The arithmetic typing check requires the computation result to
already have the target type; narrowing, promoted narrow targets and mixed-type
computations needing conversions absent from the direct children remain loud.
These are statements only: assignment values within larger expressions still
refuse. No compound computation type is guessed from a `qualType` string.

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
binary and logical returns, captured `if`/`while`/`do` branches, parameter stores,
prefix/postfix increment and decrement admission, conditional-expression
branch typing, comma-expression sequencing, loop transfers, compound-assignment
target/type/evidence mismatches and function-try refusals.
`extractors/cpp/test_evidence_ingestion.py` has an opt-in pinned Clang check for
real admitted bodies, including every compound operator, unsigned wraparound,
self-aliasing and assignment-driven loops. It also checks prefix/postfix
increment and decrement, unsigned wraparound, and loud refusal of narrow and
mixed-type compound destinations. The same explicit compiler/plugin settings
are required; missing settings skip rather than count as agreement. Broader
conversions and statements still need semantic models, and `Translation.execute`
remains refused.
