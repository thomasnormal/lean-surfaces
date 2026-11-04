# Void callable results

2026-10-20. N4950 [basic.fundamental] and [stmt.return]
distinguish a void result from an integral value. A non-coroutine void function
may return with `return;` or by reaching its closing brace. Neither produces an
integer. Both end the callee's automatic objects; reference parameters do not
own the caller's objects.

The structured Clang type projection represents builtin `void` as
`CppTypeEvidence.void`. Callable admission permits it only as a result;
parameters retain the existing integral value/lvalue-reference restriction.
An empty `ReturnStmt` lowers to `CallableStatement.returnVoid` only in a void
function. A nonempty return in a void function remains loud, including a
void-valued expression: calls and casts to void need their own expression
semantics. No `qualType` spelling establishes this result type.

The object evaluator's `evaluateCallableObjectResultInFrame`,
`evaluateCallableObjectResultInStore` and `evaluateCallableObjectResult`
return `IntegralResult (Option IntegralValue)`: successful `none` is void,
successful `some value` is integral. Undefined/invalid/unsupported computations
and frame errors retain their state and remain distinct from a successful void
return. Normal void fallthrough and explicit void return clean up the callee;
early return skips all subsequent effects. Integral fallthrough remains a
`missingReturn` failure. The existing integral-only object APIs and value-only
evaluator refuse a void signature before executing its body. The legacy frame
API preserves its existing zero-fuel `fuelExhausted` priority.

This adds no call-expression dispatch, external function implementation,
temporary binding, pointer/array/class value, exception or coroutine semantics.
Clang capture and source-to-IR lowering remain trusted; bounded compiler
controls are not proofs of arbitrary original C++ programs.
