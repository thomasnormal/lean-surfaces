# C frontend census: C23 rejects and C17 fallback

This report reruns the pinned Clang on the 350 files rejected under C23.
It uses Clang diagnostics and modes directly; it does not parse source text.

- survey commit: `e646567600c850eb9af9645aaa7a0c6944b7b2cd`
- survey measured at: `2026-11-12T15:45:35Z`
- frontend: `clang version 21.1.8 (https://github.com/conda-forge/clangdev-feedstock 334cf9a5e6c0331e9f261eaf01fc3568724fcce9)`
- profile flags: `-D_FORTIFY_SOURCE=0`
- C23 rejected: **349**
- C17 accepted: **56**
- C17 still rejected: **293**

## C23 first diagnostic classes

| class | files |
| --- | ---: |
| `use of undeclared identifier 'asm'` | 72 |
| `a type specifier is required for all declarations` | 49 |
| `function definition is not allowed here` | 23 |
| `unknown type name 'x'` | 20 |
| `unknown type name 'f'` | 18 |
| `'chk.h' file not found` | 16 |
| `fields must have a constant size` | 8 |
| `too many arguments to function call, expected 0, have 1` | 7 |
| `unknown type name 'a'` | 6 |
| `unknown type name 'g'` | 4 |
| `'memcpy-ax.h' file not found` | 4 |
| `use of undeclared identifier 'random'` | 4 |
| `unknown type name 'foo'` | 3 |
| `'gcc_tmpnam.h' file not found` | 3 |
| `incompatible function pointer types passing 'void (void)' to parameter of type '__sighandler_t' (aka 'void (*)(int)') [-Wincompatible-function-pointer-types]` | 3 |
| `invalid parameter name` | 3 |
| `expected ';' after top level declarator` | 3 |
| `address of register variable requested` | 3 |
| `use of undeclared identifier 'alloca'` | 2 |
| `redeclaration of C++ built-in type 'bool'` | 2 |
| `unknown type name 'p'` | 2 |
| `unknown type name 'd'` | 2 |
| `unknown type name 'b'` | 2 |
| `unknown type name 's1'` | 2 |
| `use of undeclared identifier '__builtin_mul_overflow_p'` | 2 |
| `GNU decimal type extension not supported` | 2 |
| `use of undeclared identifier '__builtin_shuffle'` | 2 |
| `use of undeclared identifier '__builtin_has_attribute'` | 2 |
| `expected expression` | 2 |
| `"FLT_SNAN undefined"` | 2 |
| `unknown type name 'fmt'` | 1 |
| `unknown type name 'name'` | 1 |
| `use of undeclared identifier 'f'` | 1 |
| `unknown type name 'p0'` | 1 |
| `unknown type name 'writes'` | 1 |
| `unknown type name 'convs'` | 1 |
| `unknown type name 'data'` | 1 |
| `unknown type name 'insn'` | 1 |
| `use of undeclared identifier '__builtin_exit'; did you mean '__builtin_abort'?` | 1 |
| `expected identifier` | 1 |
| `use of undeclared identifier 'foo'; did you mean 'for'?` | 1 |
| `call to undeclared library function 'abort' with type 'void (void) __attribute__((noreturn))'; ISO C99 and later do not support implicit function declarations [-Wimplicit-function-declaration]` | 1 |
| `chained comparison 'X < Y <= Z' does not behave the same as a mathematical expression [-Wparentheses]` | 1 |
| `use of undeclared identifier '__builtin_puts'` | 1 |
| `unknown type name 'ip'` | 1 |
| `unknown type name 'w'` | 1 |
| `unknown type name 's'` | 1 |
| `unknown type name 't'` | 1 |
| `unknown type name 'oip'` | 1 |
| `unknown type name 'str'` | 1 |
| `unknown type name 'j'` | 1 |
| `call to undeclared library function 'exit' with type 'void (int) __attribute__((noreturn))'; ISO C99 and later do not support implicit function declarations [-Wimplicit-function-declaration]` | 1 |
| `unknown type name 'sub3'` | 1 |
| `incompatible function pointer types assigning to 'double (*)(void)' from 'double (*)(double)' [-Wincompatible-function-pointer-types]` | 1 |
| `unknown type name 'orig'` | 1 |
| `unknown type name 'sub1'` | 1 |
| `unknown type name 'mr_TR'` | 1 |
| `unknown type name 'cp'` | 1 |
| `unknown type name 'value'` | 1 |
| `unknown type name 'pdbl'` | 1 |
| `unknown type name 'flags'` | 1 |
| `unknown type name 'arg'` | 1 |
| `unknown type name 'pattern'` | 1 |
| `array is too large (4611686018427387648 elements)` | 1 |
| `use of undeclared identifier '__builtin_imaxabs'` | 1 |
| `use of undeclared identifier '__builtin_fprintf_unlocked'` | 1 |
| `use of undeclared identifier '__builtin_fputs'` | 1 |
| `use of undeclared identifier '__builtin_putchar'` | 1 |
| `use of undeclared identifier '__builtin_uabs'` | 1 |
| `conflicting types for 'malloc'` | 1 |
| `unknown type name 'u'` | 1 |
| `unknown type name 'f1'` | 1 |
| `use of undeclared identifier '__builtin_nansf16b'` | 1 |
| `invalid suffix 'f128' on floating constant` | 1 |
| `use of undeclared identifier '__builtin_nansf128x'` | 1 |
| `use of undeclared identifier '__builtin_nansf32'` | 1 |
| `use of undeclared identifier '__builtin_nansf32x'` | 1 |
| `use of undeclared identifier '__builtin_nansf64'` | 1 |
| `use of undeclared identifier '__builtin_nansf64x'` | 1 |
| `expected identifier or '('` | 1 |
| `use of undeclared identifier '__builtin_exit'` | 1 |
| `too many arguments to function call, expected 0, have 2` | 1 |
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
| `c-testsuite/single-exec` | `00209.c` | `c6e49de1a1042f763ef0a443865b655ccfae63e374755924820423ff7914fc75` |
| `gcc.c-torture/execute` | `20000112-1.c` | `ed81908d74dd6f920ee3cfa46c06fbb2f469310f48f3e7c6d39707b088d5af6f` |
| `gcc.c-torture/execute` | `20000314-3.c` | `06bd1936f096dda238eebe9d0cf19d0045686205e7c02c03fe03af39cd80660d` |
| `gcc.c-torture/execute` | `20000726-1.c` | `f2332b741c1dc67c2e44c1983630503eaa71b6dd7a3d08d4752b5f9503ab93bd` |
| `gcc.c-torture/execute` | `20000808-1.c` | `9587ac2547140cf096915e059dc4c5605778185b000f95d67ca0918e01802d49` |
| `gcc.c-torture/execute` | `20000815-1.c` | `187e949d8da043e7536179a7ca04f5e5d0337a3cec9bcf3612d784ba0a8235c0` |
| `gcc.c-torture/execute` | `20000914-1.c` | `9c4c365fb6325fd3d8e324732f33a597f8b09446f2f509202e7be978b5189df7` |
| `gcc.c-torture/execute` | `20001026-1.c` | `e368d8a4fefb57c20cfbe79f4fe0e5a4822e4e7cb719f64868439643db932c83` |
| `gcc.c-torture/execute` | `20001101.c` | `eab613ff0506f5a395de4c05e8723593a96fe8c08b74e097fd1ce6406d463176` |
| `gcc.c-torture/execute` | `20020404-1.c` | `f5f91edded3a8567ad743ab424dc8ab903db5e2fe828af56f492e165a5a8da26` |
| `gcc.c-torture/execute` | `20030714-1.c` | `ef808ee2e3bf489b2aed2d93ce63aee4ddbae9b14688c40a700dcdbd43d9dd5c` |
| `gcc.c-torture/execute` | `20051012-1.c` | `9d1dc628e7796fec5cb8295c52f933e08383391af64a610366220300bf351f73` |
| `gcc.c-torture/execute` | `20170401-2.c` | `a3745f4dd83d768de318635057f1fd8df12a1664b1a9b97fe0e29cd75e0e931b` |
| `gcc.c-torture/execute` | `20190820-1.c` | `d275097bf205290a0773cc75ce5c9ebe6c8c10820b0675e44bcb80bfa3d781fb` |
| `gcc.c-torture/execute` | `920302-1.c` | `ebcf15377317e655ba378a31413ec0ca49e8f17c3c357d94de6af2d2a6514dc4` |
| `gcc.c-torture/execute` | `920501-2.c` | `8c6b9532202bfeebc626121c8b10a36410385e65d338a18c297058e165fd1572` |
| `gcc.c-torture/execute` | `920501-3.c` | `4a7fba430dcb1498eb2dcef680482a27978fb54c7b3faf4e3235310be4ada66e` |
| `gcc.c-torture/execute` | `920501-6.c` | `8e4a8ab4982190f5fb064ab17693bb13a244eff5188750c7bf0cafb08c924366` |
| `gcc.c-torture/execute` | `920604-1.c` | `d9ffd9d4c15e4b62c12d49341ae42769201f89166dc2eb33692f460e87b5ae57` |
| `gcc.c-torture/execute` | `920612-1.c` | `de6c38b41524218d47bd31889256c11a0ea2258255c8c06accea18b9b14072f5` |
| `gcc.c-torture/execute` | `920922-1.c` | `40b68280ace97b110beac6e8f018f866a90c712af1fd560f22a4fb102d826684` |
| `gcc.c-torture/execute` | `921112-1.c` | `48eae00775562f119d027a680cd7a47e9decf5b693fc83e8117dd5ebe00fdf33` |
| `gcc.c-torture/execute` | `930608-1.c` | `1a585f2362d3d8d71437cfdaf216e7a2e7a15249cbc6b875c656248b19c886f8` |
| `gcc.c-torture/execute` | `931005-1.c` | `0b6ee7e6b9324fe4473f522b2338bf6a45ce1ec9bb58cf269c711d1c3aeedc92` |
| `gcc.c-torture/execute` | `941015-1.c` | `72434740e03a14eb8f8399a39ee8463706f806c26f86080662d2e89167417561` |
| `gcc.c-torture/execute` | `941021-1.c` | `02edbb4e717f3304408d76c8d1a181af0965167073e4d94b16a4dc5d3a19a136` |
| `gcc.c-torture/execute` | `941025-1.c` | `c77cca036c29a733a7c0fee664fa46e4e5d691b4c0cd99ba3ec9107104491d6f` |
| `gcc.c-torture/execute` | `950221-1.c` | `f6a8c353c345293df9d70ad696351de1b2d49b21d43ef3f9c55134c77fc3e09b` |
| `gcc.c-torture/execute` | `960209-1.c` | `5d33f700691c3a9e4c6abebcec95753117be5c91cc5776ded82e4e96dd728a2b` |
| `gcc.c-torture/execute` | `960419-1.c` | `ff74f3f66f754262ba87fad2662c8b7df116b5e49bb9f2a93a581179bcd6bf22` |
| `gcc.c-torture/execute` | `960513-1.c` | `aec9013b5cb129ca5bc6843a31910d156e156d9dc508cf646679491e5f518e60` |
| `gcc.c-torture/execute` | `960608-1.c` | `aa862abc34900560fda1095219421213dfd37a182a5afe44915dd4f4b342a690` |
| `gcc.c-torture/execute` | `960909-1.c` | `73201b7ef3827531016043632de78d5f51fa930653128e3b255672ccab2a5a8d` |
| `gcc.c-torture/execute` | `961026-1.c` | `bb9bc83f164ed0b3901bc512d5996ae26e88ef0c1ec8880318f725048625dbbe` |
| `gcc.c-torture/execute` | `970923-1.c` | `73bc74112e9e16d63ad3a760d123acb9db36c1faf45bec7c2ad5c5f4bdf1f891` |
| `gcc.c-torture/execute` | `980506-1.c` | `52ddbd0e4b743cae90223460d4cc3337aaffa37483dca2603129efdf400b2b42` |
| `gcc.c-torture/execute` | `980506-3.c` | `4084e640ff4402df02bc1614665961f054137d1eefb3ad0c59e487154deb1867` |
| `gcc.c-torture/execute` | `980526-3.c` | `969abcbd2cfb8d0dcfdeea6bfe189b8fec5f30bb30945b5b2f01db8ed7832288` |
| `gcc.c-torture/execute` | `981130-1.c` | `2ea419b7b761423bc19a5417f60d8e2f84a0a2bfd5ca834a374763a548153f61` |
| `gcc.c-torture/execute` | `comp-goto-1.c` | `47075d49b5eeb8662241b4e72a7e930b19bd89460c3ec00b2f7cd4229fed7f8f` |
| `gcc.c-torture/execute` | `conversion.c` | `c71be59f131b7f95cd2ae58238422b205bc599446d9ed77fdfad68730bf2947b` |
| `gcc.c-torture/execute` | `ieee/920810-1.c` | `e0b670c899b3364a884f07ef9f25c4f91da6ec0026cf5112ffd3f1d691fcfa6c` |
| `gcc.c-torture/execute` | `ieee/fp-cmp-1.c` | `8a7bfcc539016effffd02dd0a10ebadc609fc0d801553f479c6963747a6c47c9` |
| `gcc.c-torture/execute` | `ieee/fp-cmp-2.c` | `eca8e59a0d72a02cac0b6fbc982d22d46d34c65ac9e84436e59f4635de09394b` |
| `gcc.c-torture/execute` | `ieee/fp-cmp-3.c` | `21380bf459e475b978fd790de0ae12bd5a773d90b3b477f614c6a3f940303bfd` |
| `gcc.c-torture/execute` | `ieee/fp-cmp-4.c` | `893ffaf92751c977c481ee29c311d64d17d7a08c9c24d591f19d9aa75b094f16` |
| `gcc.c-torture/execute` | `ieee/fp-cmp-4f.c` | `fc005ba136e4c7d09df682f663d25666a916eb0e7567534b70523f187d1c9f33` |
| `gcc.c-torture/execute` | `ieee/fp-cmp-4l.c` | `3cd2dfdbd3688e7c33991c53efdb874ee1eb4362391da0f44f7ffe39a0c62bc1` |
| `gcc.c-torture/execute` | `loop-9.c` | `54bdbc85e3110ad2728c4ab8817a1f309708ffd5306e2a315710b4bc818fdb43` |
| `gcc.c-torture/execute` | `pending-4.c` | `c8d69da8db6c6d7bc9652effa9082bbbe41d9732c44569cbb6a3c51b9619cf93` |
| `gcc.c-torture/execute` | `pr103209.c` | `3d6a68abb19587f0b45be734966c8c62cd91d6682a066f563931b2f8a01ed441` |
| `gcc.c-torture/execute` | `pr28289.c` | `833579b35d14df9ea4f49d01fc7812717db75000985c5b37aacf96dbe2d0d8eb` |
| `gcc.c-torture/execute` | `pr34982.c` | `8d285eafcf8a8ee7b6ca3660bcfaadbacafcc3752b23e823dd49b2e03d9b8708` |
| `gcc.c-torture/execute` | `pr67037.c` | `e1a96eafc068b577cb7d5814345558e5dfad24bbc578389dff1644fd969fc318` |
| `gcc.c-torture/execute` | `va-arg-2.c` | `3f1f43cf070b5103f384bda5e96482340b8a21bdb2d801bcce3a2b459fbde81e` |
| `gcc.c23-run` | `gcc/testsuite/gcc.dg/cpp/c23-trigraphs-2.c` | `932d60f9807cc471b9fdf807096171dcc99383beba89e208bce188576734baa7` |

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
