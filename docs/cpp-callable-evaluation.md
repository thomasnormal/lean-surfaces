# C++ direct-return callable evaluation

`LeanModels/Cpp/CallableEvaluation.lean` evaluates the already-admitted
`CallableFunction` profile without changing the translation execution boundary.
It accepts positional `IntegralValue` arguments, checks their exact parameter
formats, evaluates integer literals, parameter references and typed integral
binary expressions, and returns the existing `IntegralResult` so signed
overflow, division errors, shift errors and unsupported arithmetic remain
visible rather than becoming host-language behavior.

Evaluation has explicit fuel. A zero budget is a loud `fuelExhausted` refusal;
no recursive execution is hidden behind a partial definition. The evaluator is
not wired to `Translation.execute`, does not admit branches, loops, local
objects, calls or conversions outside the retained typed expression tree, and
makes no claim about Clang or compiled execution.

## Checks

```sh
lake build LeanModels.Cpp.CallableEvaluationTests
```

The guards cover identity, integer literal and binary addition results, signed
overflow, arity/profile refusal and fuel exhaustion.
