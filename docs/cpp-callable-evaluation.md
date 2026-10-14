# C++ callable statement evaluation

`LeanModels/Cpp/CallableEvaluation.lean` evaluates the already-admitted
`CallableFunction` statement profile without changing the translation execution boundary.
It accepts positional `IntegralValue` arguments, converts each valid argument
to the declared parameter format with the existing profile-checked integral
conversion, evaluates integer literals, parameter references, integral casts,
typed integral unary and binary expressions, and short-circuiting logical `&&`/`||` inside
sequences, `if` branches and `while`/`do`/`for` loops. Parameter-targeted `=`,
integral compound-assignment statements and prefix/postfix parameter
increment/decrement expressions thread updated argument values through later
statements. Loop-local `break` and `continue` transfer control to the nearest
admitted `while`/`do` loop. Typed conditional expressions evaluate their condition once and
only evaluate the selected branch. Comma expressions evaluate their left
operand first, retain its updated parameter state, and evaluate the right
operand only after a successful left result. The evaluator returns the existing
`IntegralResult` so signed
overflow, division errors, shift errors and unsupported arithmetic remain visible
rather than becoming host-language behavior.

N4950 §7.6.1.3 [expr.call] initializes every parameter from its corresponding
argument. This boundary therefore converts and validates all supplied arguments
before entering the body, including unused parameters. The already-computed
values have no side effects; the positional traversal does not select a C++
argument-expression evaluation order. Integer conversions use §7.3.9
[conv.integral], with boolean destinations following [conv.bool]. Defaults,
variadic arguments, references and user-defined conversions remain outside this
boundary.

Compound assignments evaluate their admitted, side-effect-free RHS, read the
target parameter once, compute using the shared `integralBinary` operation and
store only a successful result. The admission profile requires the arithmetic
result format to equal the destination format, so no implicit narrowing is
invented here. The updated state feeds subsequent branches and loop conditions;
arithmetic failures propagate instead of executing later statements.

Prefix and postfix increment/decrement follow the admitted parameter-only shape
of [expr.pre.incr] and [expr.post.incr]: the target is updated once, prefix
returns the updated value, and postfix returns the saved value. The update uses
the target's profile-resolved integral format, so unsigned wraparound is an
`IntegralResult.ok` result while signed overflow remains
`IntegralResult.undefined`. An increment nested in an unsequenced binary
operand is rejected rather than assigning an evaluation order.

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

An admitted `for` loop is evaluated as its initializer followed by a
state-threaded `while`: the condition runs before each body, and the step runs
after each normally completing body. The profile rejects condition declarations
and omitted conditions. A `continue` in the outer `for` body runs the lowered
loop step before rechecking its condition; nested `while`/`do` transfers remain
owned by their inner loop.

An admitted `switch` has an exact builtin `int` condition and a compound body made
of literal `case` labels and at most one `default`. Labels are unique. Matching
starts at the first matching case, or at `default`, and ordinary completion
falls through later clauses in source order. A `break` exits the switch; return and evaluation failures propagate. `continue`
anywhere inside a switch subtree remains outside the admitted profile, even if
an inner loop would own the transfer. This conservative admission guard is
necessary because the lowered `for` step is not rewritten inside switch clauses.
Non-constant labels,
duplicate labels and malformed clause bodies remain loud refusals.

`break` exits the nearest admitted `while`/`do` loop or `switch`. `continue` skips the
remaining body and rechecks the loop condition (with a `do` loop's usual
post-body check); both transfers retain the current parameter state. A transfer
that reaches the public callable boundary is a typed refusal.

Logical `&&` and `||` retain their sequencing guarantee even when the right
operand increments a parameter: the right side is evaluated only when the left
side selects it, and its updated state contributes to the boolean result.

Evaluation has explicit fuel. A zero budget is a loud `fuelExhausted` refusal;
no recursive execution is hidden behind a partial definition. The evaluator is
not wired to `Translation.execute`, and does not admit local objects, calls,
overload resolution or general implicit-conversion semantics.
Falling through
without a return is a typed `missingReturn` refusal.
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
including unsigned wraparound, self-aliasing and state updates through `while`
and `do`/`for`/`switch` control flow with `break`/`continue`. It compares the evaluator with 244 Clang-compiled calls at both
`-O0` and `-O2`, under undefined-behavior sanitization, and separately checks two
loud compound-conversion refusals. Width checks pin the LP64 target; missing
settings skip rather than count as agreement. This is evidence for the bounded
call profile, not whole-program execution.
