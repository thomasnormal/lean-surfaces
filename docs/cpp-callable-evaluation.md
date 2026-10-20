# C++ callable statement evaluation

`LeanModels/Cpp/CallableEvaluation.lean` is the legacy value-only evaluator for
the already-admitted `CallableFunction` statement profile; it does not change
the translation execution boundary or execute object-backed local nodes.
`CallableObjectEvaluation.lean` evaluates the same callable tree against an
`IntegralObjectFrame`, including validated automatic integral declarations.
It accepts positional `IntegralValue` arguments, converts each valid argument
to the declared parameter format with the existing profile-checked integral
conversion, evaluates integer literals, parameter references, integral casts,
typed integral unary and binary expressions, and short-circuiting logical `&&`/`||` inside
sequences, `if` branches and `while`/`do`/`for` loops. Parameter-targeted `=`,
integral compound-assignment statements and prefix/postfix parameter
increment/decrement expressions thread updated argument values through later
statements. Loop-local `break` and `continue` transfer control to the nearest
admitted `while`/`do`/`for` loop. Typed conditional expressions evaluate their condition once and
only evaluate the selected branch. Comma expressions evaluate their left
operand first, retain its updated parameter state, and evaluate the right
operand only after a successful left result. The evaluator returns the existing
`IntegralResult` so signed
overflow, division errors, shift errors and unsupported arithmetic remain visible
rather than becoming host-language behavior. A return carries a returned result
only after its expression succeeds; an integral failure remains a failure with
the active frame retained for the caller.

N4950 §7.6.1.3 [expr.call] initializes every parameter from its corresponding
argument. This boundary therefore converts and validates all supplied arguments
before entering the body, including unused parameters. The already-computed
values have no side effects; the positional traversal does not select a C++
argument-expression evaluation order. Integer conversions use §7.3.9
[conv.integral], with boolean destinations following [conv.bool]. Defaults,
variadic arguments, references and user-defined conversions remain outside this
boundary.

Both evaluators form each admitted literal in its structured source type,
including `bool`, unsigned integers and integers wider than `int`. An enclosing
integral conversion remains a separate expression node. Thus `1u` can take
part in unsigned arithmetic and `4294967296L` does not acquire an artificial
32-bit range failure in the value-only evaluator.

Compound assignments evaluate their admitted, side-effect-free RHS, read the
target parameter once, compute using the shared `integralBinary` operation and
store only a successful result. The operator is validated before the RHS is
evaluated, so an unknown spelling cannot mask its loud refusal with an operand
failure. The admission profile requires the arithmetic
result format to equal the destination format, so no implicit narrowing is
invented here. The updated state feeds subsequent branches and loop conditions;
arithmetic failures propagate instead of executing later statements.

Unary and binary operators are validated before their operands are evaluated,
so an unknown spelling cannot mask its refusal with an operand failure.

Prefix and postfix increment/decrement follow the admitted integral binding shape
of N4950 §7.6.2.3 [expr.pre.incr] and §7.6.1.6 [expr.post.incr]: the target is updated once, prefix
returns the updated value, and postfix returns the saved value. An increment
operator outside `++` and `--` is a loud refusal before the parameter is read,
rather than an assumed decrement. The arithmetic follows the compound-assignment
rule §7.6.19 [expr.ass]: combine the target with an `int` one using §7.3.7
[conv.prom] and §7.4 [expr.arith.conv], then convert the successful result back
to the target type under §7.3.9 [conv.integral] before storing it. Both
evaluators use this sequence.
On LP64, incrementing `short(32767)` computes `int(32768)` and stores
`short(-32768)`; decrementing `short(-32768)` stores `short(32767)`. These
conversions are defined C++23 behavior. Prefix returns the converted stored
value, while postfix returns the original value after completing that store.
Unsigned arithmetic wraps; signed overflow in the computation type remains
`IntegralResult.undefined` and leaves the stored value unchanged. An increment
nested in an unsequenced binary operand is rejected rather than assigning an evaluation order.

Conditional expressions preserve the C++ sequencing boundary between their
condition and selected arm. A selected arm may update the parameter through an
admitted increment/decrement; the unselected arm is not evaluated. The
evaluator requires both arms to have the same represented builtin type and does
not guess the usual conditional conversions.

Comma expressions follow the C++ left-to-right sequencing rule. Their operands
must be builtin integral expressions, and the represented result type must be
the right operand's type. A failed left operand propagates without evaluating
the right operand; side effects nested below either operand remain visible to
the admission check rather than being treated as unsequenced.

Ordinary compound statements retain explicit `block` boundaries, including empty
and singleton blocks. N4950 §8.4 [stmt.block] and §8.6.4 [stmt.for] supply
the block and loop structure. In this value-only evaluator, a local declaration
remains a loud refusal; the object-backed evaluator enters and exits the
corresponding frame scopes and allocates its validated integral objects.

An admitted `forLoop` executes its initializer once, then tests the condition
before each body. Normal body completion and `continue` execute the step once
before the next test. Break, return and failure bypass the step; a failed step
bypasses the next condition. A failed body evaluation remains a failure while
unwinding the loop and enclosing blocks, so the callable frame retains its
active outer scope instead of being mistaken for a returned value. A failed
initializer also unwinds the loop scope before retaining that outer frame.
Nested loops consume their own transfers. The
profile still rejects condition declarations and omitted conditions. No
step-before-continue rewrite remains. A separate iteration helper recurs without
re-entering the initializer, and every iteration checks its fuel budget.

An admitted `switch` has an exact builtin `int` condition and a compound body made
of literal `case` labels and at most one `default`. The switch body gets its own
lexical frame scope; clause locals are ended on normal, transfer and typed
failure unwinding. Labels are unique. Matching
starts at the first matching case, or at `default`, and ordinary completion
falls through later clauses in source order. A `break` exits the switch; return and evaluation failures propagate. `continue`
passes through switches and reaches its nearest enclosing iteration statement.
An outer `for` runs its step on that path, exactly once, after the switch and
body have propagated the transfer. Inner loops consume their own transfers.
Non-constant labels, duplicate labels and malformed clause bodies remain loud refusals.

`break` exits the nearest admitted `while`/`do`/`for` loop or `switch`. `continue` skips the
remaining body and rechecks the loop condition (with a `do` loop's usual
post-body check); both transfers retain the current parameter state. A transfer
that reaches the public callable boundary is a typed refusal.

Logical `&&` and `||` retain their sequencing guarantee even when the right
operand increments a parameter: the right side is evaluated only when the left
side selects it, and its updated state contributes to the boolean result.
Other logical operator spellings are refused rather than interpreted as one of
those two short-circuit forms.

Evaluation has explicit fuel. A zero budget is a loud `fuelExhausted` refusal;
the expression and statement evaluators in both paths recurse structurally on
that budget. The object frame's expression and statement execution does likewise.
Scope cleanup instead descends the finite scope stack, and switch fallthrough
descends the selected clause suffix using the already-smaller statement evaluator.
Those finite traversals consume no additional fuel, preserving the existing
depth budgets and retained failure state. Increment reads retain their original
fuel checks through a nonrecursive parameter-read helper.

These execution definitions reduce in Lean's kernel; no recursive execution is
hidden behind a `partial` definition or well-founded recursion. The kernel
regressions use `rfl` for local mutation, loops, switch fallthrough and transfers,
cleanup, narrow increment conversion and retained overflow state, and print
their axiom inventories (at most the core `propext` axiom). Native `#guard`
execution alone would not establish
that property. Frontend JSON parsing and callable admission still use runtime
parsers; this execution refactor does not establish a kernel-reducible ingestion
pipeline or a theorem about an original corpus function.

The evaluator is
not wired to `Translation.execute`, and does not admit local objects in its
value-only path, calls,
overload resolution or general implicit-conversion semantics.
Falling through
without a return is a typed `missingReturn` refusal for an integral result.
Void fallthrough succeeds through the result API described below.
It does not establish Clang conformance or general compiled-execution coverage.

## Checks

```sh
lake build LeanModels.Cpp.CallableEvaluationTests
LEANCPP_TEST_LEAN=1 python3 extractors/cpp/test_evidence_ingestion.py
```

The guards cover identity, short/unsigned/boolean argument conversion, boolean
destinations, unused-argument validation, invalid argument values, integer
literal, binary addition and logical short-circuit results, captured
`if`/`while`/`do`/`for` branches, prefix/postfix increment and decrement,
conditional branch selection, comma sequencing, loop transfers, signed overflow,
arity/profile refusal and fuel exhaustion.

The optional compiled check also requires explicit matching `LEANCPP_CLANG` and
`LEANCPP_PROBE_LIBRARY` settings. It probes identity and literal bodies, skipped
and discarded statements, branches, unary/binary/logical operators, integral
return casts, parameter assignments, prefix/postfix increment/decrement,
conditional expressions, comma sequencing, `for` loops, loop transfers and
effectful logical short-circuiting.
All ten compound operators are covered,
including nested and empty blocks, once-only loop initialization, false initial
conditions, return-before-step, unsigned wraparound, self-aliasing and state updates through `while`
and `do`/`for`/`switch` control flow with `break`/`continue`. It compares both evaluators with 318 Clang-compiled calls at both
`-O0` and `-O2`, under undefined-behavior sanitization, and separately checks two
loud compound-conversion refusals. Width checks pin the LP64 target; missing
settings skip rather than count as agreement. This is evidence for the bounded
call profile, not whole-program execution.

Void functions use the [result API](cpp-void-callables.md), where successful
`none` denotes no value. The integral-only APIs refuse a void result before
executing the body.
