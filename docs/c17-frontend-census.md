# C frontend census: C23 rejects and C17 fallback

This report reruns the pinned Clang on the 350 files rejected under C23.
It uses Clang diagnostics and modes directly; it does not parse source text.

- survey commit: `1d5ce79d2`
- survey measured at: `2026-11-13T10:29:45Z`
- frontend: `clang version 21.1.8 (https://github.com/conda-forge/clangdev-feedstock 334cf9a5e6c0331e9f261eaf01fc3568724fcce9)`
- profile flags: `-D_FORTIFY_SOURCE=0`
- C23 rejected: **293**
- C17 accepted: **0**
- C17 still rejected: **293**

## C23 first diagnostic classes

| class | files |
| --- | ---: |
| `use of undeclared identifier 'asm'` | 72 |
| `a type specifier is required for all declarations` | 49 |
| `function definition is not allowed here` | 23 |
| `unknown type name 'f'` | 18 |
| `'chk.h' file not found` | 16 |
| `unknown type name 'x'` | 10 |
| `fields must have a constant size` | 8 |
| `unknown type name 'g'` | 4 |
| `'memcpy-ax.h' file not found` | 4 |
| `use of undeclared identifier 'random'` | 4 |
| `unknown type name 'foo'` | 3 |
| `'gcc_tmpnam.h' file not found` | 3 |
| `expected ';' after top level declarator` | 3 |
| `address of register variable requested` | 3 |
| `use of undeclared identifier 'alloca'` | 2 |
| `unknown type name 'b'` | 2 |
| `use of undeclared identifier '__builtin_mul_overflow_p'` | 2 |
| `GNU decimal type extension not supported` | 2 |
| `use of undeclared identifier '__builtin_shuffle'` | 2 |
| `use of undeclared identifier '__builtin_has_attribute'` | 2 |
| `expected expression` | 2 |
| `"FLT_SNAN undefined"` | 2 |
| `use of undeclared identifier 'f'` | 1 |
| `use of undeclared identifier '__builtin_exit'; did you mean '__builtin_abort'?` | 1 |
| `too many arguments to function call, expected 0, have 1` | 1 |
| `use of undeclared identifier 'foo'; did you mean 'for'?` | 1 |
| `call to undeclared library function 'abort' with type 'void (void) __attribute__((noreturn))'; ISO C99 and later do not support implicit function declarations [-Wimplicit-function-declaration]` | 1 |
| `chained comparison 'X < Y <= Z' does not behave the same as a mathematical expression [-Wparentheses]` | 1 |
| `use of undeclared identifier '__builtin_puts'` | 1 |
| `unknown type name 'w'` | 1 |
| `unknown type name 's'` | 1 |
| `unknown type name 'd'` | 1 |
| `call to undeclared library function 'exit' with type 'void (int) __attribute__((noreturn))'; ISO C99 and later do not support implicit function declarations [-Wimplicit-function-declaration]` | 1 |
| `unknown type name 'sub3'` | 1 |
| `unknown type name 's1'` | 1 |
| `unknown type name 'orig'` | 1 |
| `unknown type name 'sub1'` | 1 |
| `unknown type name 'mr_TR'` | 1 |
| `unknown type name 'cp'` | 1 |
| `array is too large (4611686018427387648 elements)` | 1 |
| `use of undeclared identifier '__builtin_imaxabs'` | 1 |
| `use of undeclared identifier '__builtin_fprintf_unlocked'` | 1 |
| `use of undeclared identifier '__builtin_fputs'` | 1 |
| `use of undeclared identifier '__builtin_putchar'` | 1 |
| `use of undeclared identifier '__builtin_uabs'` | 1 |
| `unknown type name 'f1'` | 1 |
| `use of undeclared identifier '__builtin_nansf16b'` | 1 |
| `invalid suffix 'f128' on floating constant` | 1 |
| `use of undeclared identifier '__builtin_nansf128x'` | 1 |
| `use of undeclared identifier '__builtin_nansf32'` | 1 |
| `use of undeclared identifier '__builtin_nansf32x'` | 1 |
| `use of undeclared identifier '__builtin_nansf64'` | 1 |
| `use of undeclared identifier '__builtin_nansf64x'` | 1 |
| `unknown type name 'a'` | 1 |
| `use of undeclared identifier '__builtin_exit'` | 1 |
| `'../../gcc.dg/tree-ssa/pr105777.c' file not found` | 1 |
| `address of vector element requested` | 1 |
| `'../../gcc.dg/tree-ssa/pr109938.c' file not found` | 1 |
| `'../../gcc.dg/tree-ssa/pr109986.c' file not found` | 1 |
| `use of undeclared identifier '__builtin_exit'; did you mean '__builtin_trap'?` | 1 |
| `cannot decrement value of type 'W' (vector of 4 'short' values)` | 1 |
| `initialization of flexible array member is not allowed` | 1 |
| `'../../gcc.dg/tree-ssa/pr30314.c' file not found` | 1 |
| `use of undeclared identifier '__builtin_isinff'` | 1 |
| `use of undeclared identifier '__builtin_apply'` | 1 |
| `illegal storage class on file-scoped variable` | 1 |
| `'../../gcc.dg/pr98304-1.c' file not found` | 1 |
| `unknown type name 'feq'` | 1 |
| `use of undeclared identifier '__builtin_va_arg_pack'` | 1 |
| `'_Atomic' qualifier ignored; operations involving the enumeration type will be non-atomic [-Wunderlying-atomic-qualifier-ignored]` | 1 |
| `"DBL_SNAN undefined"` | 1 |
| `"LDBL_SNAN undefined"` | 1 |
| `assigning to '_Atomic(bool)' from incompatible type 'nullptr_t'` | 1 |
| `member reference base type 'typeof (*(1 ? &s ` | 1 |
| `use of undeclared identifier '__builtin_clear_padding'` | 1 |
| `variable has incomplete type 'typeof (*(1 ? &x ` | 1 |
| `redeclaration of 'i' with a different type` | 1 |
| `invalid suffix 'D32' on floating constant` | 1 |
| `use of undeclared identifier 'DEC64X_MAX'` | 1 |

## C17 flip set

These files parse under C17 with the same pinned profile and are the registered candidates for the next mode-aware extractor run.

| corpus | file | sha256 |
| --- | --- | --- |

## C17 remaining diagnostic classes

| class | files |
| --- | ---: |
| `type specifier missing, defaults to 'int'; ISO C99 and later do not support implicit int [-Wimplicit-int]` | 74 |
| `use of undeclared identifier 'asm'` | 49 |
| `function definition is not allowed here` | 23 |
| `call to undeclared function 'asm'; ISO C99 and later do not support implicit function declarations [-Wimplicit-function-declaration]` | 23 |
| `'chk.h' file not found` | 16 |
| `fields must have a constant size` | 8 |
| `parameter 'x' was not declared, defaults to 'int'; ISO C99 and later do not support implicit int [-Wimplicit-int]` | 6 |
| `parameter 'b' was not declared, defaults to 'int'; ISO C99 and later do not support implicit int [-Wimplicit-int]` | 4 |
| `'memcpy-ax.h' file not found` | 4 |
| `call to undeclared function 'typeof'; ISO C99 and later do not support implicit function declarations [-Wimplicit-function-declaration]` | 4 |
| `ISO C requires a named parameter before '...'` | 4 |
| `use of unknown builtin '__builtin_exit' [-Wimplicit-function-declaration]` | 3 |
| `parameter 'i' was not declared, defaults to 'int'; ISO C99 and later do not support implicit int [-Wimplicit-int]` | 3 |
| `parameter 'a' was not declared, defaults to 'int'; ISO C99 and later do not support implicit int [-Wimplicit-int]` | 3 |
| `'gcc_tmpnam.h' file not found` | 3 |
| `expected ';' after top level declarator` | 3 |
| `address of register variable requested` | 3 |
| `call to undeclared library function 'exit' with type 'void (int) __attribute__((noreturn))'; ISO C99 and later do not support implicit function declarations [-Wimplicit-function-declaration]` | 2 |
| `call to undeclared function 'alloca'; ISO C99 and later do not support implicit function declarations [-Wimplicit-function-declaration]` | 2 |
| `call to undeclared library function 'abort' with type 'void (void) __attribute__((noreturn))'; ISO C99 and later do not support implicit function declarations [-Wimplicit-function-declaration]` | 2 |
| `parameter 'y' was not declared, defaults to 'int'; ISO C99 and later do not support implicit int [-Wimplicit-int]` | 2 |
| `parameter 'm' was not declared, defaults to 'int'; ISO C99 and later do not support implicit int [-Wimplicit-int]` | 2 |
| `use of unknown builtin '__builtin_mul_overflow_p' [-Wimplicit-function-declaration]` | 2 |
| `GNU decimal type extension not supported` | 2 |
| `use of unknown builtin '__builtin_shuffle' [-Wimplicit-function-declaration]` | 2 |
| `use of unknown builtin '__builtin_has_attribute' [-Wimplicit-function-declaration]` | 2 |
| `expected expression` | 2 |
| `"FLT_SNAN undefined"` | 2 |
| `call to undeclared function 'f'; ISO C99 and later do not support implicit function declarations [-Wimplicit-function-declaration]` | 1 |
| `call to undeclared function 'foo'; ISO C99 and later do not support implicit function declarations [-Wimplicit-function-declaration]` | 1 |
| `chained comparison 'X < Y <= Z' does not behave the same as a mathematical expression [-Wparentheses]` | 1 |
| `use of unknown builtin '__builtin_puts' [-Wimplicit-function-declaration]` | 1 |
| `parameter 'got' was not declared, defaults to 'int'; ISO C99 and later do not support implicit int [-Wimplicit-int]` | 1 |
| `parameter 'n' was not declared, defaults to 'int'; ISO C99 and later do not support implicit int [-Wimplicit-int]` | 1 |
| `parameter 'com' was not declared, defaults to 'int'; ISO C99 and later do not support implicit int [-Wimplicit-int]` | 1 |
| `array is too large (4611686018427387648 elements)` | 1 |
| `use of unknown builtin '__builtin_imaxabs' [-Wimplicit-function-declaration]` | 1 |
| `use of unknown builtin '__builtin_fprintf_unlocked' [-Wimplicit-function-declaration]` | 1 |
| `use of unknown builtin '__builtin_fputs' [-Wimplicit-function-declaration]` | 1 |
| `use of unknown builtin '__builtin_putchar' [-Wimplicit-function-declaration]` | 1 |
| `use of unknown builtin '__builtin_uabs' [-Wimplicit-function-declaration]` | 1 |
| `use of unknown builtin '__builtin_nansf16b' [-Wimplicit-function-declaration]` | 1 |
| `invalid suffix 'f128' on floating constant` | 1 |
| `use of unknown builtin '__builtin_nansf128x' [-Wimplicit-function-declaration]` | 1 |
| `use of unknown builtin '__builtin_nansf32' [-Wimplicit-function-declaration]` | 1 |
| `use of unknown builtin '__builtin_nansf32x' [-Wimplicit-function-declaration]` | 1 |
| `use of unknown builtin '__builtin_nansf64' [-Wimplicit-function-declaration]` | 1 |
| `use of unknown builtin '__builtin_nansf64x' [-Wimplicit-function-declaration]` | 1 |
| `'../../gcc.dg/tree-ssa/pr105777.c' file not found` | 1 |
| `address of vector element requested` | 1 |
| `'../../gcc.dg/tree-ssa/pr109938.c' file not found` | 1 |
| `'../../gcc.dg/tree-ssa/pr109986.c' file not found` | 1 |
| `cannot decrement value of type 'W' (vector of 4 'short' values)` | 1 |
| `initialization of flexible array member is not allowed` | 1 |
| `'../../gcc.dg/tree-ssa/pr30314.c' file not found` | 1 |
| `use of unknown builtin '__builtin_isinff' [-Wimplicit-function-declaration]` | 1 |
| `use of unknown builtin '__builtin_apply' [-Wimplicit-function-declaration]` | 1 |
| `illegal storage class on file-scoped variable` | 1 |
| `'../../gcc.dg/pr98304-1.c' file not found` | 1 |
| `use of unknown builtin '__builtin_va_arg_pack' [-Wimplicit-function-declaration]` | 1 |
| `"DBL_SNAN undefined"` | 1 |
| `"LDBL_SNAN undefined"` | 1 |
| `use of undeclared identifier 'nullptr'` | 1 |
| `expected function body after function declarator` | 1 |
| `invalid suffix 'D32' on floating constant` | 1 |
| `expected parameter declarator` | 1 |
