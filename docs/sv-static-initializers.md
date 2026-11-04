# Residual static initializers — ordering and effects boundary

IEEE 1800-2023 §§6.21 and 9.3 initialize variables with static lifetime before
processes begin. The initializer is still an expression with source-order,
storage, package, macro and system-function dependencies. A closed pure value
can use the existing pre-process `Var` initialization; an initializer that
reads runtime storage, calls a system or random function, depends on package
state, or requires a conversion not represented by the value tier needs its
own evaluation and ordering contract.

## Why residual `StaticLocal:initializer` remains a boundary

The procedural-lifetime tier preserves static storage and retains the value on
re-entry. It admits a source-ordered dependency only when both declarations
are in the same procedural scope and every initializer is already a closed
pure value. Runtime reads, effects, random or environment calls, package or
qualified dependencies, and cross-scope ordering remain outside the envelope.
Evaluating those forms as zero, dropping them, or running them as an ordinary
process would change before-entry visibility and can reorder effects or random
draws. No second scheduler is introduced.

## 2026-10-27 — source-ordered pure dependencies

Static locals now retain source order within each procedural scope. A later
initializer may read an earlier static declaration after the existing purity
and expression checks pass; declarations in another scope and pre-process
module initializers still produce `StaticLocal:initializer-order`. The
`static_dependency_initializer` fixture checks a four-state value read by a
zero-shift result and its Lean self-check receipt.

The capped 22,065-file chapter census moves from **5,331 clean / 16,667
partial** to **5,359 clean / 16,639 partial** with 67 include skips;
`StaticLocal:initializer` falls **168 → 140**. The remaining 140 files still
need runtime, effect, cross-scope, or ordering contracts.

## 2026-10-22 census and decision

The fresh 22,043-path census records `StaticLocal:initializer` in **167**
files: **40** are initializer-only and **127** co-occur with another wall.
The read-only repricer finds **47** unsupported initializer spans in the sole
files:

| source shape | spans | files |
|---|---:|---:|
| static initializer | 47 | 40 |
| random or constrained-random call | 9 | 9 |
| system-function call | 13 | 12 |
| macro expansion | 3 | 3 |
| package or qualified read | 2 | 2 |
| type or size cast | 7 | 5 |
| real conversion | 6 | 2 |
| shift expression | 5 | 5 |
| power expression | 3 | 3 |
| bitwise expression | 5 | 5 |
| conditional expression | 1 | 1 |
| aggregate assignment pattern | 1 | 1 |
| nonliteral source | 47 | 40 |
| runtime-dependent read | 39 | 36 |

Rows overlap. Reproduce the measurement with:

```text
python3.9 extractors/sv/static_initializer_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reports source shapes only. It does not evaluate random calls,
choose an initializer order, or turn a nonclosed initializer into a constant.
