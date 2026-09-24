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
batteries (`*_lab`), and steps along the sunfish arc (`sf_*`). They build
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

**Capstone:** [`sunfish`](sunfish/) is the unmodified 673-line
[sunfish](https://github.com/thomasahle/sunfish) chess engine
(GPL-3.0, see its header). The whole
file loads. The flagship theorems are proved over the real opening
position with a symbolic score, for example
`Position.rotate` negating the score (`rotate_callsIn`). Its other
`.lean` files are the research log for the search function.

To learn the tactics, start with [docs/tutorial/](../../docs/tutorial/index.md).
Proofs that fail in instructive ways are collected in
[tutorial 06](../../docs/tutorial/06-when-proofs-fail.md).
