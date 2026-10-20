# Typed source-local callable functions

2026-10-20. `LeanModels/Cpp/Callable.lean` extends the first **callable body
admission** through the typed automatic-local declaration rule. It is
intentionally a small, typed C++23 profile; it is not a C++ execution engine.
A function is admitted only when its declaration, direct parameters,
structured function type, declaration evidence and retained body all agree in
the same Clang probe.

## Admitted profile

The candidate must be a named ordinary `FunctionDecl` or a witnessed static
`CXXMethodDecl`, accepted by `admitLocalFunctionDeclaration` with a direct
`CompoundStmt` body. Static methods require the getter and canonical record
context checks described in [static callables](cpp-static-callables.md). Prototypes,
deleted declarations and function-try bodies remain loud refusals. The body
retains ordinary `CompoundStmt` nodes as `block` boundaries containing
sequences of admitted expression statements, `if` statements with an optional
else branch, `while`/`do`/bounded `for` loops,
integral `switch` statements with literal `case`/`default` labels, loop-local
`break`/`continue`, parameter/local-targeted `=`, integral compound
assignments, parameter/local-targeted prefix/postfix increment and decrement
expressions, and validated automatic integral `DeclStmt` nodes. The latter
cover copy, direct, list and default scalar initialization, multiple
declarators and lexical shadowing through the object-backed frame. An empty
compound is `block skip`; a null statement is `skip`. Unsupported storage,
reference results, temporary/rvalue bindings, arrays, aliases, calls,
overloaded operations, exceptions, local functions and every other statement
form refuse rather than being silently represented as a callable.

The function type comes from the validated `Clang::QualType structured type
projection v1` row for the exact occurrence. This slice requires a non-variadic
signature with a builtin integral result and nonvolatile integral value or
lvalue-reference parameters. Const value parameters retain their object/access qualification;
lvalue-to-rvalue conversion removes it before arithmetic.
Every direct `ParmVarDecl` must have a matching type-evidence row, and its type
must agree, in order, with the function type's parameter list. The result type
is retained as structured `CppTypeEvidence`; no `qualType` string is used to
decide the function signature.

The return-expression profile is:

- a nonnegative decimal `IntegerLiteral` with a witnessed builtin integral type
  (legacy captures require exact builtin `int`), or a `CXXBoolLiteralExpr`;
- a parameter `DeclRefExpr`, through only `LValueToRValue` or `NoOp`
  `ImplicitCastExpr` wrappers; or
- an integral `ImplicitCastExpr` (`IntegralToBoolean` or `IntegralCast`) over
  an admitted operand, with a builtin integral destination; or
- a unary integral `+`, `-`, `~` or `!` expression over an admitted operand; or
- a prefix or postfix `++`/`--` over a direct non-boolean integral parameter
  or admitted-local reference; or
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

### Expression type preservation

N4950 §7.3.7 `[conv.prom]`, §7.3.9 `[conv.integral]`, §7.3.15
`[conv.bool]` and §7.6.2.2 `[expr.unary.op]` govern the conversions before
unary evaluation. In particular, negating the minimum `short` first promotes
it to `int`; complementing an `unsigned char` also operates in the promoted
type. A surrounding boolean conversion must observe that promoted result.

The callable boundary requires a structured type for each lowered value expression
when the probe supplies `Clang::Expr type projection v1`. Rows join only through
the retained AST's root/`inner` tree, with occurrence/kind consensus and known
type references. Casts retain their actual destination types, and unary
operand/result types must agree with the target profile's promotion rules.
The whole raw AST remains available; `qualType` spellings do not establish
these destinations. Missing child rows in a supplied supplement refuse.
For a batch of functions, `admitCallableFunctionWithExpressionTypes` consumes
rows already validated from that same probe. The ordinary
`admitCallableFunction` entry point validates this supplement itself. Each
body keeps only its own occurrence rows after whole-probe validation; this
retains the same checks while avoiding unrelated rows during expression lookup.

Legacy captures can retain expressions whose types are established by the
existing signature and binary evidence. An integral cast with no witnessed
destination refuses instead of copying its operand's type. This compatibility
path cannot silently erase promotion before a unary operation.

The result type of the expression must equal the function result type. A
parameter or admitted-local reference must resolve to one of the function's
own declaration handles. Missing rows, mismatched handles, changed child order, unsupported
casts, non-integral operators, unsequenced side effects in ordinary binary
operands and
conflicting evidence all refuse. Increment and decrement require a directly bound
parameter or admitted local; members, calls and overloaded operators remain outside
this profile. Conditional expressions with
an omitted middle operand, unrepresented conversions or mismatched branch
types remain loud refusals.

Comma expressions retain C++'s left-to-right sequencing boundary. Their left
operand must complete successfully before the right operand is evaluated, and
effectful expressions nested beneath either operand are rejected when they
would otherwise be unsequenced inside a binary expression.

The admitted `for` shape has an automatic-local-capable initializer and step,
an explicit integral condition, and an admitted body. A first-class `forLoop`
retains the initializer, condition, step and body separately; condition
declarations and omitted conditions remain loud refusals. The initializer runs once. Normal
body completion and `continue` reach the step after the body returns; `break`,
return and failure skip the step. Inner loops consume their own transfers.
`break` and `continue` remain loud at the public boundary when no loop or
switch consumes them. No body rewriting inserts a step inside a source block.

The admitted `switch` shape has an exact builtin `int` condition and a compound body
whose clauses use unique literal integer `case` labels and at most one `default`.
The `switch_` node retains that compound boundary around the clause list; nested
compound statements within clauses retain their own `block` nodes.
Execution starts at the matching case or default and falls through later clauses
until a `break`, return or failure. Label uniqueness is checked over every
clause, including duplicate cases or defaults after an unrelated first label.
`continue` passes through switch clauses to its nearest enclosing loop. An
outer `for` then executes its own step once; an inner loop consumes its own
transfers before returning to that outer body. A switch consumes its own
`break` without exiting an enclosing loop. Unsupported labels and
malformed clauses still refuse.

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

The object-backed callable profile consumes the
[automatic integral declaration contract](cpp-local-declarations.md). Its
legacy value-only evaluator remains loud on `CallableStatement.automatic`
nodes; only the object-backed evaluator executes those declarations with
preserved bindings, scopes and cleanup.

## Validation

`LeanModels/Cpp/CallableTests.lean` covers identity, literal, typed integral
binary and logical returns, captured `if`/`while`/`do` branches, parameter stores,
prefix/postfix increment and decrement admission, conditional-expression
branch typing, comma-expression sequencing, loop transfers, complete switch-label
uniqueness and switch/loop transfer ownership, compound-assignment
target/type/evidence mismatches, automatic local declaration admission and
function-try refusals.
`extractors/cpp/test_evidence_ingestion.py` has an opt-in pinned Clang check for
real admitted bodies, including every compound operator, unsigned wraparound,
self-aliasing and assignment-driven loops. It also checks prefix/postfix
increment and decrement, unsigned wraparound, and loud refusal of narrow and
mixed-type compound destinations. Real compiler fixtures also check admission
and execution of switch-contained `continue` under `while`, `for`, `do`, nested
loops and nested switches, with ordinary switch/break as a positive control.
Conditional transfers and skipped trailing side effects distinguish the correct
nearest-loop behavior from accidentally executing an outer step inside an inner
loop. The same explicit
compiler/plugin settings are required; missing settings skip rather than count
as agreement. Broader
conversions and statements still need semantic models, and `Translation.execute`
remains refused.

Automatic integral lvalue references execute through the object-backed frame:
`int &r = value; ++r; return value;` observes the shared object. Their expression
types are their referent types. Const views preserve const access, and lexical
cleanup removes alias bindings without ending the referent. Reference parameters
are supported through the [shared caller-store boundary](cpp-reference-parameters.md);
reference results remain outside the callable signature profile. The value-only
evaluator continues to refuse automatic declarations. See
[reference execution](cpp-reference-types.md#local-reference-execution-boundary).

The generic `extractors/cpp/export_callable.lean` validates a complete probe
before exporting one admitted typed body as a kernel-reducible Lean literal.
The [TinyXML-2 example](../Examples/cpp/tinyxml2/README.md) uses this path for
an original static helper and proves its entire signed-char input domain.
