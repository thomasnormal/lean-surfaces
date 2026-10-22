# Package subroutine boundary — retained callable declarations

`Package:Subroutine` marks a function or DPI import declared in a package.
Package functions participate in elaboration-time constant evaluation and in
runtime calls through package scopes; DPI imports carry an external ABI and
linkage. The legacy envelope has no package callable table, constant-function
evaluator or DPI boundary representation.

## Why package subroutines remain loud

IEEE 1800-2023 §§13.4.3 and 26.2 permit package functions in constant
expressions and make their declarations visible through imports and generated
scopes. A DPI import additionally names an external implementation and calling
convention. Dropping an unused declaration would hide an invalid or externally
bound name, while flattening a function into one call would lose scope and
reusable frame identity. No package callable is erased, inlined or replaced by
a guessed external result, and no second evaluator or scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `Package:Subroutine` in **194** files;
**10** are sole refusals and 184 co-occur. The independent read-only repricer
finds **12** unsupported package-subroutine spans in the sole files:

| source shape | spans | files |
|---|---:|---:|
| package function declaration | 10 | 8 |
| constant-function use | 9 | 7 |
| nonconstant package function | 1 | 1 |
| DPI import | 2 | 2 |

The constant-use and function-declaration labels overlap. Reproduce the table
with:

```text
python3.9 extractors/sv/package_subroutine_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
shapes without evaluating package functions or resolving external DPI code.
