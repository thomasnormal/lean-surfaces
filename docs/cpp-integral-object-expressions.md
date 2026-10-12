# C++ integral object expressions

`IntegralObjectExpressions.lean` is the next stateful rung above the integral
object store. It evaluates a small typed-value fragment with explicit fuel:
integral literals, reads through validated object accesses, and integral unary
and binary operators. Expression-driven assignment evaluates the source, then uses the
object store's profile-checked conversion boundary before publishing a value.

Reads observe the current object slot, so aliases see the same writes and ended
or released objects refuse. The evaluator propagates the existing integral
invalid, undefined and unsupported results rather than using host arithmetic.
Fuel exhaustion is explicit; no partial or general C++ execution is hidden.

The fragment does not admit calls, branches, loops, pointer arithmetic, object
construction, overloaded operators, references as values, volatile access,
floating/enum/record values, or implicit conversion rules beyond the explicit
builtin-integral source/destination boundary. Unary and binary evaluation uses
the admitted integral value kernel; promotion and usual-arithmetic type
selection remain a separate typing boundary. `Translation.execute` remains
refused, and no whole-program execution claim is made.

## Checks

```sh
lake build LeanModels.Cpp.IntegralObjectExpressionTests
```

The guards cover alias reads, unary and binary results, expression assignment, conversion,
fuel exhaustion, invalid literals, stale reads and const-write refusal. The
integral object Clang differential suite remains the independent value oracle;
this stateful expression layer adds no new compiler or corpus admission claim.
