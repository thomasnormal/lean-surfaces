# Python examples — a curated path

Each example is a directory `<name>/` in the three-file layout:

- `<name>.py` is the program.
- `spec.lean` holds the concrete `#py_check` runs and every theorem
  statement.
- `proof.lean` holds the proofs.

Build one with `lake build Examples.python.<name>.spec`. Do not run a bare
`lake build`, which builds every tier.

Read the ten below in order. Each one adds a single new idea. The other
directories here are tutorial companions (`tut_*`), semantic regression
batteries (`*_lab`), and small benchmark programs (`bench_*`). They build
and they are checked, but they are not written to be read first.

| # | example | what it shows | headline statement |
|---|---|---|---|
| 1 | [`add`](add/) | the judgment arrows `==>` (total) and `~~>` (partial) | `add(a, b) ==> a + b` |
| 2 | [`my_abs`](my_abs/) | one branch point, `py_prove` | `my_abs(x) ==> \|x\|` |
| 3 | [`midpoint`](midpoint/) | Python `//` is floor division (`Int.fdiv`), and why a sign hypothesis matters | `midpoint(a, b) ==> Int.fdiv (a + b) 2` |
| 4 | [`tri`](tri/) | the first loop: an invariant and a measure with `py_vcgen` | `tri(n) ==> n * (n + 1) / 2` |
| 5 | [`gcd`](gcd/) | a loop that mutates its parameters (a private core with renamed binders); preconditions found by differential testing | `gcd(a, b) ==> Int.gcd a b` |
| 6 | [`fib`](fib/) | recursion: strong induction on the mathematical argument, never on fuel | `fib(k) ==> fibSpec k` |
| 7 | [`nested_flow`](nested_flow/) | nested loops, `break`, and a `return` inside a loop | `first_factor(n) ==> n.toNat.minFac` |
| 8 | [`rsa_inverse`](rsa_inverse/) | real code (python-rsa 4.9.1, vendored verbatim) with a relational `∃`-result spec | Bézout coefficients of `extended_gcd` |
| 9 | [`bench_bisect`](bench_bisect/) | CPython's own `bisect_left`, where a loop variable is created inside the loop | the result is the insertion point on sorted input |
| 10 | [`bench_statistics`](bench_statistics/) | CPython's `statistics.median_low/high`, through builtin `sorted` | the result is the order statistic |

For decimal parsing, [`int_string`](int_string/) combines concrete grammar and
exception checks with symbolic proofs: `int("1_024") + offset` equals
`1024 + offset`, and a signed, whitespace-padded literal yields `offset - 2048`.
Non-ASCII strings, more than 640 decimal digits, and explicit bases stay loud.

[`ann_lab`](ann_lab/) proves that a module global annotated with a forward-reference
string remains available to ordinary symbolic function proofs. Its kernel checks
also pin the refusal of effectful module annotations; function-local annotation
erasure remains independent of that module-scope restriction.

[`bool_lab`](bool_lab/) proves integer nonzero truthiness and Boolean identity
symbolically. Concrete checks cover heap containers, default instances, closures,
nondraining generator truthiness, argument effects, and excess-argument errors;
custom truthiness protocols and first-class builtin type values stay loud.

[`decimal_render`](decimal_render/) proves that `str(value)` returns the exact
decimal string when `value.natAbs < 10 ^ 640`. The same magnitude admission
guards integer fields in container and range rendering and bare `%s`/`%r`/`%d`;
larger values refuse rather than guessing CPython's configurable digit limit.

[`range_render`](range_render/) proves that `str(range(value))` retains the
Boolean `True` or `False` spelling for symbolic `value : PyBool`. Constructor
fields retain their scalar objects; numerical consumers project them to integers.
Its concrete checks cover rendering routes, numerical consumers, and exceptions.

[`string_repeat`](string_repeat/) proves both operand orders and a decorated
result for symbolic text and counts. The admission premises bound the original
count magnitude and output code-point length to 1,048,576; excessive counts
stay loud even when the string is empty or the count is negative.

[`tuple_repeat`](tuple_repeat/) proves symbolic repeated-tuple lengths and the
empty-tuple result under the same original-count bound. The output-element
count also stays within 1,048,576; excessive counts refuse even for negative
counts and empty tuples. Its concrete checks cover both operand orders, `*=`,
namedtuple-to-tuple results, and shared heap references.

**Sunfish:** the proofs about the unmodified
[sunfish](https://github.com/thomasahle/sunfish) chess engine (GPL-3.0)
now live in the sunfish repository, as a Lake package that depends on
this one. That includes the `sf_*` examples, which proved excerpts and
simplified forms of sunfish functions.

To learn the tactics, start with [docs/tutorial/](../../docs/tutorial/index.md).
Proofs that fail in instructive ways are collected in
[tutorial 06](../../docs/tutorial/06-when-proofs-fail.md).
