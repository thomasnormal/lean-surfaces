# C++ callable statement evaluation

`LeanModels/Cpp/CallableEvaluation.lean` evaluates the already-admitted
`CallableFunction` statement profile without changing the translation execution boundary.
It accepts positional `IntegralValue` arguments, converts each valid argument
to the declared parameter format with the existing profile-checked integral
conversion, evaluates integer literals, parameter references, integral casts,
typed integral unary and binary expressions, and short-circuiting logical `&&`/`||` inside
sequences, `if` branches and `while`/`do` loops, and returns the existing `IntegralResult` so signed
overflow, division errors, shift errors and unsupported arithmetic remain
visible rather than becoming host-language behavior.

N4950 §7.6.1.3 [expr.call] initializes every parameter from its corresponding
argument. This boundary therefore converts and validates all supplied arguments
before entering the body, including unused parameters. The already-computed
values have no side effects; the positional traversal does not select a C++
argument-expression evaluation order. Integer conversions use §7.3.9
[conv.integral], with boolean destinations following [conv.bool]. Defaults,
variadic arguments, references and user-defined conversions remain outside this
boundary.

Evaluation has explicit fuel. A zero budget is a loud `fuelExhausted` refusal;
no recursive execution is hidden behind a partial definition. The evaluator is
not wired to `Translation.execute`, does not admit `for` loops, local
objects, calls, overload resolution or general implicit-conversion semantics.
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
`if`/`while`/`do` branches, signed overflow, arity/profile refusal and fuel
exhaustion.

The optional compiled check also requires explicit matching `LEANCPP_CLANG` and
`LEANCPP_PROBE_LIBRARY` settings. It probes real signed, unsigned, short,
unsigned-short and boolean identity bodies and a two-parameter first-value body,
then compares the admitted evaluator against their Clang-compiled calls for 115
rows at both `-O0` and `-O2`, with undefined-behavior sanitization. Width checks
pin the LP64 target; missing settings skip rather than count as agreement. This
is evidence for the bounded call profile, not whole-program execution.
