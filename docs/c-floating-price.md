# C floating-literal frontend price

- survey commit: `391e289b317a58006fe9ee46308c84b0f3ccf6a8`
- survey measured at: `2026-11-12T16:12:00Z`
- sole dynamic wall: `unsupported:floating literal (floats are a named decision)`
- candidate files: **39**
- all parser-native records joined: **True**
- bit widths present: `{32: 10, 64: 32, 80: 10}`
- types present: `{'double': 32, 'float': 10, 'long double': 10}`

| corpus | file | literals | widths | types | static walls |
| --- | --- | ---: | --- | --- | --- |
| `gcc.c-torture/execute` | `20020720-1.c` | 2 | `[64]` | `['double']` | `libc-call, type-layout` |
| `gcc.c-torture/execute` | `20030914-1.c` | 2 | `[80]` | `['long double']` | `cast:IntegralToFloating, type-layout` |
| `gcc.c-torture/execute` | `20080502-1.c` | 4 | `[64, 80]` | `['double', 'long double']` | `cast:FloatingCast, libc-call, type-layout` |
| `gcc.c-torture/execute` | `20080529-1.c` | 1 | `[32]` | `['float']` | `type-layout` |
| `gcc.c-torture/execute` | `920501-8.c` | 1 | `[64]` | `['double']` | `libc-call, string-literal, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `941021-1.c` | 2 | `[64]` | `['double']` | `type-layout` |
| `gcc.c-torture/execute` | `980205.c` | 4 | `[64]` | `['double']` | `libc-call, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `980605-1.c` | 2 | `[64]` | `['double']` | `cast:FloatingToIntegral, cast:IntegralToFloating, libc-call, string-literal, type-layout` |
| `gcc.c-torture/execute` | `990127-2.c` | 6 | `[64]` | `['double']` | `type-layout` |
| `gcc.c-torture/execute` | `990826-0.c` | 2 | `[64]` | `['double']` | `libc-call, type-layout` |
| `gcc.c23-run` | `gcc/testsuite/gcc.dg/c23-digit-separators-1.c` | 2 | `[32]` | `['float']` | `type-layout, unsupported:StaticAssertDecl` |
| `gcc.c23-run` | `gcc/testsuite/gcc.dg/c23-float-1.c` | 6 | `[32, 64, 80]` | `['double', 'float', 'long double']` | `type-layout` |
| `gcc.c23-run` | `gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c` | 58 | `[32, 64]` | `['double', 'float']` | `cast:FloatingCast, cast:IntegralToFloating, libc-call, type-layout` |
| `gcc.c-torture/execute` | `ieee/20010226-1.c` | 5 | `[80]` | `['long double']` | `cast:FloatingToIntegral, type-layout` |
| `gcc.c-torture/execute` | `ieee/920810-1.c` | 1 | `[64]` | `['double']` | `cast:IntegralToFloating, libc-call, string-literal, type-layout` |
| `gcc.c-torture/execute` | `ieee/compare-fp-2.c` | 2 | `[64]` | `['double']` | `cast:FloatingToIntegral, type-layout` |
| `gcc.c-torture/execute` | `ieee/fp-cmp-7.c` | 1 | `[64]` | `['double']` | `libc-call, type-layout` |
| `gcc.c-torture/execute` | `ieee/inf-2.c` | 3 | `[32, 64, 80]` | `['double', 'float', 'long double']` | `libc-call, type-layout` |
| `gcc.c-torture/execute` | `ieee/inf-3.c` | 3 | `[32, 64, 80]` | `['double', 'float', 'long double']` | `libc-call, type-layout` |
| `gcc.c-torture/execute` | `ieee/mzero4.c` | 24 | `[32, 64]` | `['double', 'float']` | `libc-call, type-layout` |
| `gcc.c-torture/execute` | `ieee/mzero6.c` | 4 | `[64]` | `['double']` | `libc-call, type-layout` |
| `gcc.c-torture/execute` | `ieee/pr108540-1.c` | 2 | `[64]` | `['double']` | `cast:IntegralToFloating, libc-call, string-literal, type-layout` |
| `gcc.c-torture/execute` | `ieee/pr108540-2.c` | 8 | `[64]` | `['double']` | `libc-call, type-layout` |
| `gcc.c-torture/execute` | `ieee/pr109008.c` | 6 | `[64]` | `['double']` | `libc-call, type-layout` |
| `gcc.c-torture/execute` | `ieee/pr119002.c` | 1 | `[32]` | `['float']` | `libc-call, string-literal, type-layout` |
| `gcc.c-torture/execute` | `ieee/pr36332.c` | 1 | `[80]` | `['long double']` | `libc-call, type-layout` |
| `gcc.c-torture/execute` | `pr39501.c` | 144 | `[32, 64]` | `['double', 'float']` | `type-layout` |
| `gcc.c-torture/execute` | `pr44942.c` | 31 | `[64, 80]` | `['double', 'long double']` | `libc-call, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `pr64979.c` | 2 | `[64]` | `['double']` | `libc-call, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `pr67929_1.c` | 2 | `[32]` | `['float']` | `cast:FloatingToIntegral, libc-call, type-layout` |
| `gcc.c-torture/execute` | `stdarg-4.c` | 12 | `[64]` | `['double']` | `cast:FloatingToIntegral, libc-call, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `va-arg-12.c` | 15 | `[64]` | `['double']` | `libc-call, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `va-arg-15.c` | 9 | `[64]` | `['double']` | `cast:IntegralToFloating, libc-call, string-literal, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `va-arg-16.c` | 22 | `[64]` | `['double']` | `libc-call, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `va-arg-17.c` | 18 | `[64]` | `['double']` | `libc-call, string-literal, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `va-arg-18.c` | 9 | `[64]` | `['double']` | `libc-call, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `va-arg-5.c` | 16 | `[64, 80]` | `['double', 'long double']` | `libc-call, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `va-arg-6.c` | 4 | `[64, 80]` | `['double', 'long double']` | `libc-call, type-layout, unsupported:VAArgExpr` |
| `gcc.c-torture/execute` | `va-arg-7.c` | 9 | `[64]` | `['double']` | `libc-call, type-layout, unsupported:VAArgExpr` |

The 39 files are the survey's sole dynamic floating-literal wall. Every FloatingLiteral observed in their approved Clang envelopes joined to a parser-native rounded bit pattern. This prices the frontend/value boundary only; no floating semantics or flip is claimed.
