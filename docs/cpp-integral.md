# C++23 integral value semantics

`LeanModels/Cpp/Integral.lean` is the pure, kernel-reducible value layer for
built-in integral operations. It follows N4950, not ISO C's differing shift
rules. It does not admit an AST, a callable body or any program execution.
`execute` still refuses every C++ artifact.

## Representation and resolution boundary

`IntegralFormat` describes boolean values or signed/unsigned value widths;
`IntegralValue` pairs that representation with a mathematical integer. These
are **not C++ type identities**. In particular, equal widths do not identify
`int` and `long`, establish conversion ranks, identify enum types, resolve an
overload or prove that a width is available on a target. The future frontend
type bridge must check those facts against an explicit target profile.

The operation entry points `integralUnary` and `integralBinary` require values
**after** built-in operator selection, lvalue-to-rvalue conversion, integral
promotions (§7.3.7) where applicable and usual arithmetic conversions (§7.4)
where required. Logical not instead uses contextual conversion to bool.
The latter must already have produced a common operand format. Mixed formats
outside shifts and unpromoted boolean arithmetic refuse; shifts retain the
promoted left format and allow a different promoted count format. Equal
formats alone are not evidence that resolution happened. Narrow formats are
useful for conversions; this layer cannot decide whether a supplied narrow
operand was actually promoted by a target's extended-type rules.

No objects, storage, padding bytes, indeterminate values, volatile access,
references, sequencing, overloaded operators, floating point or enumeration
identity are modelled here. There are no logical binary operators: evaluating
both supplied values cannot establish short-circuit expression semantics.

## Rules and outcomes

| Entry point | N4950 rule |
| --- | --- |
| Range validation and unsigned arithmetic | §6.8.2 `[basic.fundamental]` p1–5: signed ranges, unsigned modulo arithmetic, corresponding base-2 representations. |
| `integralConvert` | §7.3.9 `[conv.integral]` p2–3: bool maps to zero/one; other destinations use the unique congruent value modulo their width. Conversion to bool follows §7.3.15 `[conv.bool]`. |
| Unary plus, minus, complement, logical not | §7.6.2.2 `[expr.unary.op]` p7–10; signed negation must stay in range. |
| Multiply, divide, remainder | §7.6.5 `[expr.mul]` p2–4: division truncates toward zero, a remainder has the dividend's sign, zero divisors and an unrepresentable quotient are undefined for both `/` and `%`. |
| Add and subtract | §7.6.6 `[expr.add]` p1–3 and §7.1 `[expr.pre]` p4: signed out-of-range results are undefined, unlike unsigned modulo arithmetic. |
| Left and right shift | §7.6.7 `[expr.shift]` p1–3: counts outside `[0, left width)` are undefined; left shift is congruent modulo the result width even for signed/negative operands; signed right shift rounds down. |
| Comparisons | §7.6.9 `[expr.rel]` and §7.6.10 `[expr.eq]`: already-converted integral operands compare by their mathematical values; results have boolean format. |
| Bitwise and/xor/or | §7.6.11–13 `[expr.bit.and]`, `[expr.xor]`, `[expr.or]`: operate on corresponding base-2 representations, then recover the result's signedness. |

`IntegralResult` separates a defined value (`ok`), invalid supplied data
(`invalid`, zero width or out-of-range integer), language undefined behavior
(`undefined`, with an explicit reason) and insufficient resolution evidence
(`unsupported`). No undefined result is an exception or a guessed value.
Only the checked entry points expose operation execution; unchecked internal
arithmetic dispatch is private. No axioms or correctness theorems are added.
Bitwise scanning recurses structurally over the explicit width rather than
using core's well-founded `Nat.bitwise`; definitional-equality guards check
reduction without native-evaluation proof tactics.

## Independent executable checks

```sh
lake build LeanModels.Cpp.IntegralTests
python3 extractors/cpp/test_integral.py
```

The Lean guards exercise boundary values and outcome distinctions. The
differential tool runs one Lean process per group and compares values with
`integral_oracle.cpp`, compiled by the selected Clang under C++23 with
`-pedantic-errors`, at both `-O0` and `-O2`, with UBSan enabled. The oracle
uses actual built-in C++ expressions and casts, not a reimplementation of
the Lean arithmetic. The compiler's C++/GCC support libraries are linked
statically (`-static-libstdc++ -static-libgcc`), so executing the probe cannot
silently select a different host C++ library. Static assertions verify the
exact-width types and
that its arithmetic operands are already promoted; compiler version and
target are printed. Override the compiler with `LEANCPP_CLANG`.

Conversions cover bool and signed/unsigned 8-, 16-, 32- and 64-bit formats;
operations cover signed/unsigned 32- and 64-bit operands. Separately executed
undefined rows require a sanitizer diagnostic and a nonzero exit, never a
native numerical result. UBSan is a diagnostic witness, not the definition
of undefined behavior. Invalid/resolution-refusal inputs are tested only on
the model because they are not valid already-resolved C++ operations.

This is standalone differential tooling, not a new CI harness registration.
Missing Clang or Lake is an explicit skip and earns no agreement. These
synthetic operation probes validate semantics; no theorem about a prototype
and no unchanged-corpus execution coverage is claimed. Type binding,
promotions, object/lifetime machinery and statement execution remain required
before this value layer can admit a function from any evidence corpus.

The rung-3 coverage witness in `IntegralRung3Tests.lean` checks defined add,
divide, remainder, bitwise-and and comparison results, while retaining signed
overflow and divide-by-zero as explicit undefined outcomes. Its native probe
executes only the defined expressions.
