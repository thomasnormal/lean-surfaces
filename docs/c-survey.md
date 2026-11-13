# C torture survey

Generated from the pinned `C1-C3 (gcc torture, c-testsuite, gcc c23-run)` manifest.

- verdicts: 992/2214 MATCH (passed 992, failed 0, oracle 0)
- manifest SHA-256: `87f487fcb8cc131926a3216c7cd55a5ba5d7cc561e55e9fd046b717a082822e7`
- measured commit: `087227a4d`
- measured at: `2026-11-13T09:37:22Z`

## Verdict counts

| verdict | files |
| --- | ---: |
| `not-parsed` | 294 |
| `oracle-tests-compiler` | 1 |
| `passed` | 992 |
| `refused-libc` | 55 |
| `refused-ub` | 105 |
| `refused-unsupported` | 701 |
| `timeout` | 66 |

## Counts by corpus

| corpus | verdict | files |
| --- | --- | ---: |
| `c-testsuite/single-exec` | `passed` | 167 |
| `c-testsuite/single-exec` | `refused-libc` | 2 |
| `c-testsuite/single-exec` | `refused-ub` | 8 |
| `c-testsuite/single-exec` | `refused-unsupported` | 41 |
| `c-testsuite/single-exec` | `timeout` | 2 |
| `gcc.c-torture/execute` | `not-parsed` | 267 |
| `gcc.c-torture/execute` | `oracle-tests-compiler` | 1 |
| `gcc.c-torture/execute` | `passed` | 822 |
| `gcc.c-torture/execute` | `refused-libc` | 51 |
| `gcc.c-torture/execute` | `refused-ub` | 96 |
| `gcc.c-torture/execute` | `refused-unsupported` | 617 |
| `gcc.c-torture/execute` | `timeout` | 64 |
| `gcc.c23-run` | `not-parsed` | 27 |
| `gcc.c23-run` | `passed` | 3 |
| `gcc.c23-run` | `refused-libc` | 2 |
| `gcc.c23-run` | `refused-ub` | 1 |
| `gcc.c23-run` | `refused-unsupported` | 43 |

## Static wall ranking

`sole` counts files whose only static wall is the named wall; `present` counts all files containing it.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `type-layout` | 366 | 1100 | 00015.c, 00016.c, 00017.c, 00018.c, 00019.c |
| `libc-call: __builtin_abort` | 158 | 379 | 20080719-1.c, 20081103-1.c, 20081218-1.c, 20110418-1.c, 20121108-1.c |
| `libc-call` | 5 | 21 | 00087.c, 00089.c, 00124.c, 00159.c, 00189.c |
| `cast:IntegralToPointer` | 3 | 29 | 00214.c, 20000314-1.c, 20000622-1.c, 20001101.c, 20010329-1.c |
| `unsequenced-effects` | 3 | 20 | 00121.c, 20001228-1.c, 20020406-1.c, 20060102-1.c, 20230802-1.c |
| `cast:PointerToIntegral` | 2 | 28 | 00144.c, 20000622-1.c, 20011121-1.c, 20030811-1.c, 20050215-1.c |
| `libc-call: malloc` | 2 | 15 | 20000914-1.c, 20020406-1.c, 20051113-1.c, 920810-1.c, 941014-2.c |
| `libc-call: __builtin_return_address` | 2 | 4 | 20010122-1.c, 20030323-1.c, 20030811-1.c, pr17377.c |
| `libc-call: memcmp` | 1 | 27 | 00179.c, 20050502-2.c, 20050826-1.c, builtins/memcmp.c, builtins/memmove-2.c |
| `libc-call: memset` | 1 | 26 | 00179.c, 20001203-2.c, 20031012-1.c, 20040823-1.c, 20050826-1.c |
| `libc-call: __builtin_memcmp` | 1 | 17 | 20081103-1.c, ieee/mzero2.c, ieee/mzero3.c, ieee/mzero5.c, pr108498-2.c |
| `unsupported:AddrLabelExpr` | 1 | 10 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920302-1.c, 920501-4.c |
| `unsupported:StmtExpr` | 1 | 10 | 00213.c, 00214.c, 20000703-1.c, 20000917-1.c, 20001203-2.c |
| `libc-call: __builtin_alloca` | 1 | 9 | 20021113-1.c, 20070824-1.c, alloca-1.c, built-in-setjmp.c, frame-address.c |
| `libc-call: __builtin_malloc` | 1 | 7 | 20071018-1.c, 20071120-1.c, pr15262-1.c, pr36765.c, pr43008.c |
| `libc-call: link_error` | 1 | 7 | 20030330-1.c, builtins/abs-2.c, builtins/complex-1.c, builtins/memcmp.c, builtins/uabs-2.c |
| `libc-call: __builtin_ffs` | 1 | 5 | builtin-bitops-1.c, ffs-1.c, ffs-2.c, pr61725.c, pr97325.c |
| `libc-call: __builtin_constant_p` | 1 | 4 | 20030330-1.c, bcp-1.c, builtin-constant.c, pr19449.c |
| `libc-call: signal` | 1 | 4 | 20101011-1.c, ieee/fp-cmp-1.c, ieee/fp-cmp-2.c, ieee/fp-cmp-3.c |
| `libc-call: calloc` | 1 | 3 | 00040.c, 20020406-1.c, ipa-sra-2.c |
| `libc-call: __builtin_abs` | 1 | 2 | pr34130.c, pr42614.c |
| `libc-call: __c11_atomic_is_lock_free` | 1 | 1 | gcc/testsuite/gcc.dg/atomic/c23-stdatomic-lockfree-char8_t.c |
| `libc-call: fun` | 1 | 1 | pr42231.c |
| `libc-call: main_test` | 1 | 1 | builtins/lib/main.c |
| `string-literal` | 0 | 270 | 00025.c, 00026.c, 00056.c, 00058.c, 00112.c |
| `cast:IntegralToFloating` | 0 | 84 | 00113.c, 00119.c, 00123.c, 00174.c, 00175.c |
| `libc-call: printf` | 0 | 73 | 00056.c, 00125.c, 00131.c, 00132.c, 00154.c |
| `libc-call: __builtin_c23_va_start` | 0 | 66 | 00204.c, 20000519-1.c, 20041113-1.c, 20071213-1.c, 920501-8.c |
| `libc-call: __builtin_va_end` | 0 | 65 | 20041214-1.c, 20071213-1.c, 920501-8.c, 920625-1.c, 920726-1.c |
| `cast:FloatingCast` | 0 | 56 | 00174.c, 00175.c, 00204.c, 20000605-1.c, 20020411-1.c |
| `libc-call: __builtin_memset` | 0 | 30 | 20000815-1.c, 20001026-1.c, 20020619-1.c, 20030606-1.c, 20030717-1.c |
| `cast:FloatingToIntegral` | 0 | 28 | 00175.c, 20000605-1.c, 20010118-1.c, 20031003-1.c, 20040709-1.c |
| `libc-call: __builtin_memcpy` | 0 | 28 | 20000703-1.c, 20011121-1.c, 20030408-1.c, 20040411-1.c, 20060930-2.c |
| `unsupported:PackedAttr` | 0 | 27 | 00210.c, 20010518-2.c, 20020227-1.c, 20030224-2.c, 20040625-1.c |
| `libc-call: strlen` | 0 | 23 | 00025.c, 00179.c, 20010409-1.c, 20011024-1.c, 20050218-1.c |
| `libc-call: strcpy` | 0 | 18 | 00179.c, 00180.c, 20031204-1.c, 20041214-1.c, 20120207-1.c |
| `libc-call: strcmp` | 0 | 16 | 00179.c, 20001011-1.c, 20011024-1.c, 20030715-1.c, 20041214-1.c |
| `libc-call: __builtin_strcmp` | 0 | 15 | 20010915-1.c, 20021011-1.c, 920302-1.c, 920501-8.c, 920726-1.c |
| `libc-call: memcpy` | 0 | 15 | 00179.c, 20010925-1.c, 20011024-1.c, 20011113-1.c, 20050826-1.c |
| `unsupported:AlignedAttr` | 0 | 15 | 20010904-1.c, 20010904-2.c, 20171008-1.c, 960117-1.c, 990326-1.c |
| `libc-call: __builtin_printf` | 0 | 14 | 20020406-1.c, 20121108-1.c, 20141022-1.c, builtins/strnlen.c, memchr-1.c |
| `libc-call: __builtin_strlen` | 0 | 14 | 20030221-1.c, 20031012-1.c, 920726-1.c, 980506-3.c, builtins/strlen.c |
| `unsupported:ImaginaryLiteral` | 0 | 13 | 20041124-1.c, 20041201-1.c, 20070614-1.c, builtins/complex-1.c, complex-1.c |
| `libc-call: sprintf` | 0 | 11 | 00186.c, 20030626-1.c, 20030626-2.c, 20070201-1.c, 920501-8.c |
| `unsupported:IndirectGotoStmt` | 0 | 10 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920302-1.c, 920501-3.c |
| `libc-call: __builtin_mul_overflow` | 0 | 9 | pr108789.c, pr64006.c, pr68381.c, pr71554.c, pr84169.c |
| `libc-call: __builtin_inf` | 0 | 8 | ieee/compare-fp-1.c, ieee/compare-fp-4.c, ieee/copysign1.c, ieee/copysign2.c, ieee/fp-cmp-7.c |
| `libc-call: __builtin_strcpy` | 0 | 8 | 20021011-1.c, 921117-1.c, 950221-1.c, builtins/strcpy.c, pr84339.c |
| `libc-call: __builtin_inff` | 0 | 7 | gcc/testsuite/gcc.dg/c23-float-2.c, gcc/testsuite/gcc.dg/c23-float-3.c, ieee/copysign1.c, ieee/copysign2.c, ieee/inf-1.c |
| `libc-call: strncmp` | 0 | 7 | 00179.c, 20050218-1.c, builtins/strncmp-2.c, builtins/strncmp.c, builtins/strstr-asm-lib.c |
| `unsupported:IndirectFieldDecl` | 0 | 7 | 00046.c, 00050.c, 00216.c, 20030714-1.c, anon-1.c |
| `libc-call: __builtin_isunordered` | 0 | 6 | ieee/compare-fp-1.c, ieee/compare-fp-3.c, ieee/compare-fp-4.c, ieee/fp-cmp-4.c, ieee/fp-cmp-5.c |
| `libc-call: __builtin_nan` | 0 | 6 | ieee/builtin-nan-1.c, ieee/compare-fp-1.c, ieee/compare-fp-4.c, ieee/copysign1.c, ieee/copysign2.c |
| `libc-call: __builtin_nanf` | 0 | 6 | gcc/testsuite/gcc.dg/c23-float-4.c, gcc/testsuite/gcc.dg/c23-float-5.c, ieee/copysign1.c, ieee/copysign2.c, ieee/pr109386.c |
| `libc-call: __builtin_prefetch` | 0 | 6 | builtin-prefetch-1.c, builtin-prefetch-2.c, builtin-prefetch-3.c, builtin-prefetch-4.c, builtin-prefetch-5.c |
| `libc-call: abs` | 0 | 6 | 20041126-1.c, builtins/abs-1.c, builtins/abs-2.c, pr33142.c, ssad-run.c |
| `libc-call: strchr` | 0 | 6 | 00179.c, 20000112-1.c, 20000910-2.c, builtins/strchr.c, builtins/strstr-asm-lib.c |
| `unsupported:DesignatedInitUpdateExpr` | 0 | 6 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-1.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-17.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-2.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-4.c |
| `unsupported:ExprWithCleanups` | 0 | 6 | 00204.c, 20020320-1.c, 20041124-1.c, 950628-1.c, gcc/testsuite/gcc.dg/c23-stdarg-9.c |
| `unsupported:GenericSelectionExpr` | 0 | 6 | 00219.c, gcc/testsuite/gcc.dg/c23-bool-1.c, gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-float-2.c, gcc/testsuite/gcc.dg/c23-float-3.c |
| `libc-call: __builtin_add_overflow` | 0 | 5 | pr108789.c, pr85095.c, pr90311.c, pr91635.c, pr93494.c |
| `libc-call: __builtin_expect` | 0 | 5 | 00214.c, 20020418-1.c, ieee/unsafe-fp-assoc-1.c, pr115277.c, pr91597.c |
| `libc-call: __builtin_infl` | 0 | 5 | ieee/copysign1.c, ieee/copysign2.c, ieee/inf-1.c, ieee/inf-2.c, ieee/pr36332.c |
| `libc-call: __builtin_longjmp` | 0 | 5 | built-in-setjmp.c, builtins/lib/chk.c, pr60003.c, pr64242.c, pr84521.c |
| `libc-call: vprintf` | 0 | 5 | builtins/lib/printf.c, printf-chk-1.c, va-arg-21.c, vprintf-1.c, vprintf-chk-1.c |
| `libc-call: __builtin_copysign` | 0 | 4 | ieee/copysign1.c, ieee/copysign2.c, ieee/mzero6.c, pr44683.c |
| `libc-call: __builtin_copysignf` | 0 | 4 | ieee/copysign1.c, ieee/copysign2.c, ieee/pr72824-2.c, ieee/pr72824.c |
| `libc-call: __builtin_islessgreater` | 0 | 4 | ieee/compare-fp-1.c, ieee/fp-cmp-4.c, ieee/fp-cmp-5.c, ieee/fp-cmp-8.c |
| `libc-call: __builtin_setjmp` | 0 | 4 | built-in-setjmp.c, pr60003.c, pr64242.c, pr84521.c |
| `libc-call: __builtin_unreachable` | 0 | 4 | 20230509-1.c, gcc/testsuite/gcc.dg/c23-unreachable-1.c, pr81281.c, pr97888-1.c |
| `libc-call: vfprintf` | 0 | 4 | builtins/lib/fprintf.c, fprintf-chk-1.c, vfprintf-1.c, vfprintf-chk-1.c |
| `unsupported:GCCAsmStmt` | 0 | 4 | 20071211-1.c, 990413-2.c, pr56982.c, pr81588.c |
| `unsupported:OffsetOfExpr` | 0 | 4 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, pr103255.c, pr30778.c, pr44468.c |
| `libc-call: __builtin_fabs` | 0 | 3 | ieee/20010114-2.c, ieee/20030331-1.c, ieee/cdivchkd.c |
| `libc-call: __builtin_huge_val` | 0 | 3 | ieee/hugeval.c, ieee/inf-1.c, ieee/inf-3.c |
| `libc-call: __builtin_isgreater` | 0 | 3 | ieee/fp-cmp-4.c, ieee/fp-cmp-5.c, ieee/fp-cmp-8.c |
| `libc-call: __builtin_isgreaterequal` | 0 | 3 | ieee/fp-cmp-4.c, ieee/fp-cmp-5.c, ieee/fp-cmp-8.c |
| `libc-call: __builtin_isless` | 0 | 3 | ieee/fp-cmp-4.c, ieee/fp-cmp-5.c, ieee/fp-cmp-8.c |
| `libc-call: __builtin_islessequal` | 0 | 3 | ieee/fp-cmp-4.c, ieee/fp-cmp-5.c, ieee/fp-cmp-8.c |
| `libc-call: __builtin_isnan` | 0 | 3 | gcc/testsuite/gcc.dg/c23-float-4.c, ieee/inf-4.c, ieee/pr108540-1.c |
| `libc-call: __builtin_signbit` | 0 | 3 | 20080502-1.c, ieee/pr108540-1.c, pr35456.c |
| `libc-call: __builtin_sprintf` | 0 | 3 | 20021120-3.c, pr78586.c, pr79327.c |
| `libc-call: __builtin_va_copy` | 0 | 3 | stdarg-1.c, va-arg-10.c, va-arg-14.c |
| `libc-call: __builtin_va_start` | 0 | 3 | 20041214-1.c, pr38151.c, va-arg-2.c |
| `libc-call: bcopy` | 0 | 3 | builtins/memmove-2.c, builtins/memmove.c, builtins/memops-asm.c |
| `libc-call: memmove` | 0 | 3 | builtins/memmove-2.c, builtins/memmove.c, string-opt-18.c |
| `libc-call: mempcpy` | 0 | 3 | builtins/mempcpy-2.c, builtins/mempcpy.c, string-opt-18.c |
| `libc-call: strncpy` | 0 | 3 | 00179.c, builtins/strncpy.c, string-opt-5.c |
| `libc-call: strrchr` | 0 | 3 | 00179.c, builtins/strrchr.c, string-opt-5.c |
| `unsupported:MaxFieldAlignmentAttr` | 0 | 3 | 20131127-1.c, pr58570.c, pr79737-1.c |
| `unsupported:MayAliasAttr` | 0 | 3 | mayalias-2.c, mayalias-3.c, pr43987.c |
| `unsupported:ModeAttr` | 0 | 3 | 20050107-1.c, 20050119-1.c, 20050119-2.c |
| `libc-call: __builtin_bswap32` | 0 | 2 | bswap-3.c, pr90025.c |
| `libc-call: __builtin_classify_type` | 0 | 2 | 20040709-1.c, 20040709-2.c |
| `libc-call: __builtin_clz` | 0 | 2 | builtin-bitops-1.c, pr37780.c |
| `libc-call: __builtin_conjf` | 0 | 2 | 20020411-1.c, builtins/complex-1.c |
| `libc-call: __builtin_copysignl` | 0 | 2 | ieee/copysign1.c, ieee/copysign2.c |
| `libc-call: __builtin_ctz` | 0 | 2 | builtin-bitops-1.c, pr37780.c |
| `libc-call: __builtin_fabsf` | 0 | 2 | ieee/cdivchkf.c, ieee/pr109386.c |
| `libc-call: __builtin_fmax` | 0 | 2 | ieee/cdivchkd.c, ieee/cdivchkf.c |
| `libc-call: __builtin_huge_valf` | 0 | 2 | ieee/inf-1.c, ieee/inf-3.c |
| `libc-call: __builtin_huge_vall` | 0 | 2 | ieee/inf-1.c, ieee/inf-3.c |
| `libc-call: __builtin_isinf` | 0 | 2 | ieee/pr108540-1.c, ieee/pr109386.c |
| `libc-call: __builtin_memmove` | 0 | 2 | builtins/memmove.c, pr93213.c |
| `libc-call: __builtin_mempcpy` | 0 | 2 | builtins/mempcpy-2.c, builtins/mempcpy.c |
| `libc-call: __builtin_nanl` | 0 | 2 | ieee/copysign1.c, ieee/copysign2.c |
| `libc-call: __builtin_stpcpy` | 0 | 2 | builtins/strpcpy-2.c, builtins/strpcpy.c |
| `libc-call: __builtin_strncpy` | 0 | 2 | builtins/strncpy.c, pr93249.c |
| `libc-call: __builtin_strstr` | 0 | 2 | builtins/strstr-asm.c, builtins/strstr.c |
| `libc-call: __builtin_trap` | 0 | 2 | 20020418-1.c, pr125291.c |
| `libc-call: _setjmp` | 0 | 2 | 20210505-1.c, pr56982.c |
| `libc-call: f` | 0 | 2 | builtins/20010124-1.c, gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: floor` | 0 | 2 | 990826-0.c, float-floor.c |
| `libc-call: fp` | 0 | 2 | 00209.c, func-ptr-1.c |
| `libc-call: fprintf` | 0 | 2 | fprintf-1.c, gofast.c |
| `libc-call: free` | 0 | 2 | ipa-sra-2.c, pr42614.c |
| `libc-call: fwrite` | 0 | 2 | 00187.c, builtins/fputs-lib.c |
| `libc-call: g` | 0 | 2 | builtins/20010124-1.c, gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: ilogb` | 0 | 2 | ieee/cdivchkd.c, ieee/cdivchkf.c |
| `libc-call: labs` | 0 | 2 | builtins/abs-1.c, builtins/abs-2.c |
| `libc-call: longjmp` | 0 | 2 | 20210505-1.c, pr56982.c |
| `libc-call: memchr` | 0 | 2 | builtins/memchr.c, memchr-1.c |
| `libc-call: mmap` | 0 | 2 | loop-2f.c, loop-2g.c |
| `libc-call: open` | 0 | 2 | loop-2f.c, loop-2g.c |
| `libc-call: sin` | 0 | 2 | 00174.c, ieee/mzero4.c |
| `libc-call: stpcpy` | 0 | 2 | builtins/strpcpy-2.c, builtins/strpcpy.c |
| `libc-call: strcat` | 0 | 2 | 00179.c, builtins/strcat.c |
| `libc-call: strstr` | 0 | 2 | builtins/strstr-asm.c, builtins/strstr.c |
| `libc-call: uabs` | 0 | 2 | builtins/uabs-1.c, builtins/uabs-2.c |
| `libc-call: ulabs` | 0 | 2 | builtins/uabs-1.c, builtins/uabs-2.c |
| `libc-call: vsprintf` | 0 | 2 | builtins/lib/chk.c, builtins/lib/sprintf.c |
| `unsupported:PredefinedExpr` | 0 | 2 | 20001011-1.c, pr58831.c |
| `unsupported:StaticAssertDecl` | 0 | 2 | gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-digit-separators-1.c |
| `unsupported:VAArgExpr` | 0 | 2 | gcc/testsuite/gcc.dg/c23-stdarg-9.c, va-arg-2.c |
| `libc-call: __assert_fail` | 0 | 1 | pr58831.c |
| `libc-call: __builtin_bcopy` | 0 | 1 | builtins/memmove.c |
| `libc-call: __builtin_bswap16` | 0 | 1 | pr97386-1.c |
| `libc-call: __builtin_bswap64` | 0 | 1 | bswap-1.c |
| `libc-call: __builtin_bzero` | 0 | 1 | builtins/memops-asm.c |
| `libc-call: __builtin_cimag` | 0 | 1 | builtins/complex-1.c |
| `libc-call: __builtin_cimagf` | 0 | 1 | builtins/complex-1.c |
| `libc-call: __builtin_cimagl` | 0 | 1 | builtins/complex-1.c |
| `libc-call: __builtin_clrsb` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_clrsbl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_clrsbll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_clzl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_clzll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_conj` | 0 | 1 | builtins/complex-1.c |
| `libc-call: __builtin_conjl` | 0 | 1 | builtins/complex-1.c |
| `libc-call: __builtin_creal` | 0 | 1 | builtins/complex-1.c |
| `libc-call: __builtin_crealf` | 0 | 1 | builtins/complex-1.c |
| `libc-call: __builtin_creall` | 0 | 1 | builtins/complex-1.c |
| `libc-call: __builtin_ctzl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_ctzll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_fabsl` | 0 | 1 | ieee/cdivchkld.c |
| `libc-call: __builtin_ffsl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_ffsll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_fmaxl` | 0 | 1 | ieee/cdivchkld.c |
| `libc-call: __builtin_frame_address` | 0 | 1 | frame-address.c |
| `libc-call: __builtin_free` | 0 | 1 | pr84339.c |
| `libc-call: __builtin_index` | 0 | 1 | builtins/strchr.c |
| `libc-call: __builtin_isfinite` | 0 | 1 | ieee/inf-4.c |
| `libc-call: __builtin_memchr` | 0 | 1 | builtins/memchr.c |
| `libc-call: __builtin_parity` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_parityl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_parityll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_popcount` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_popcountl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_popcountll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_rindex` | 0 | 1 | builtins/strrchr.c |
| `libc-call: __builtin_snprintf` | 0 | 1 | pr78622.c |
| `libc-call: __builtin_strcat` | 0 | 1 | builtins/strcat.c |
| `libc-call: __builtin_strchr` | 0 | 1 | builtins/strchr.c |
| `libc-call: __builtin_strcspn` | 0 | 1 | builtins/strcspn.c |
| `libc-call: __builtin_strncat` | 0 | 1 | builtins/strncat.c |
| `libc-call: __builtin_strncmp` | 0 | 1 | builtins/strncmp.c |
| `libc-call: __builtin_strpbrk` | 0 | 1 | builtins/strpbrk.c |
| `libc-call: __builtin_strrchr` | 0 | 1 | builtins/strrchr.c |
| `libc-call: __builtin_strspn` | 0 | 1 | builtins/strspn.c |
| `libc-call: __sync_add_and_fetch_8` | 0 | 1 | pr122000.c |
| `libc-call: alloca` | 0 | 1 | 20010122-1.c |
| `libc-call: atan` | 0 | 1 | ieee/mzero4.c |
| `libc-call: atanf` | 0 | 1 | ieee/mzero4.c |
| `libc-call: atoi` | 0 | 1 | 20221006-1.c |
| `libc-call: cimag` | 0 | 1 | builtins/complex-1.c |
| `libc-call: cimagf` | 0 | 1 | builtins/complex-1.c |
| `libc-call: cimagl` | 0 | 1 | builtins/complex-1.c |
| `libc-call: compare1` | 0 | 1 | pr34456.c |
| `libc-call: conj` | 0 | 1 | builtins/complex-1.c |
| `libc-call: conjf` | 0 | 1 | builtins/complex-1.c |
| `libc-call: conjl` | 0 | 1 | builtins/complex-1.c |
| `libc-call: creal` | 0 | 1 | builtins/complex-1.c |
| `libc-call: crealf` | 0 | 1 | builtins/complex-1.c |
| `libc-call: creall` | 0 | 1 | builtins/complex-1.c |
| `libc-call: extfunc` | 0 | 1 | pr67037.c |
| `libc-call: fabs` | 0 | 1 | 20020720-1.c |
| `libc-call: fclose` | 0 | 1 | 00187.c |
| `libc-call: fetestexcept` | 0 | 1 | gcc/testsuite/gcc.dg/c23-float-5.c |
| `libc-call: fgetc` | 0 | 1 | 00187.c |
| `libc-call: fgets` | 0 | 1 | 00187.c |
| `libc-call: fopen` | 0 | 1 | 00187.c |
| `libc-call: fprintfptr` | 0 | 1 | 00189.c |
| `libc-call: fread` | 0 | 1 | 00187.c |
| `libc-call: func` | 0 | 1 | bcp-1.c |
| `libc-call: getc` | 0 | 1 | 00187.c |
| `libc-call: h1` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h2` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h3` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h4` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h5` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h6` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h7` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: ilogbl` | 0 | 1 | ieee/cdivchkld.c |
| `libc-call: imaxabs` | 0 | 1 | builtins/abs-2.c |
| `libc-call: index` | 0 | 1 | builtins/strchr.c |
| `libc-call: indirect` | 0 | 1 | pr68390.c |
| `libc-call: isprint` | 0 | 1 | 991112-1.c |
| `libc-call: llabs` | 0 | 1 | builtins/abs-2.c |
| `libc-call: my_clrsb` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: my_clz` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: my_ctz` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: my_ffs` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: my_parity` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: my_popcount` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: not_defined` | 0 | 1 | gcc/testsuite/gcc.dg/c23-unreachable-1.c |
| `libc-call: p` | 0 | 1 | 00216.c |
| `libc-call: pow` | 0 | 1 | 980709-1.c |
| `libc-call: putchar` | 0 | 1 | 00204.c |
| `libc-call: qsort` | 0 | 1 | pr34456.c |
| `libc-call: rindex` | 0 | 1 | builtins/strrchr.c |
| `libc-call: sinf` | 0 | 1 | ieee/mzero4.c |
| `libc-call: sqrt` | 0 | 1 | ieee/20041213-1.c |
| `libc-call: strcspn` | 0 | 1 | builtins/strcspn.c |
| `libc-call: strncat` | 0 | 1 | builtins/strncat.c |
| `libc-call: strnlen` | 0 | 1 | builtins/strnlen.c |
| `libc-call: strpbrk` | 0 | 1 | builtins/strpbrk.c |
| `libc-call: strspn` | 0 | 1 | builtins/strspn.c |
| `libc-call: tan` | 0 | 1 | ieee/mzero4.c |
| `libc-call: tanf` | 0 | 1 | ieee/mzero4.c |
| `libc-call: terminate_me` | 0 | 1 | pr54937.c |
| `libc-call: ullabs` | 0 | 1 | builtins/uabs-2.c |
| `libc-call: umaxabs` | 0 | 1 | builtins/uabs-2.c |
| `libc-call: x` | 0 | 1 | 991112-1.c |
| `unsupported:BinaryConditionalOperator` | 0 | 1 | pr68249.c |
| `unsupported:CXXNullPtrLiteralExpr` | 0 | 1 | gcc/testsuite/gcc.dg/c23-nullptr-5.c |
| `unsupported:LabelDecl` | 0 | 1 | 980526-1.c |
| `unsupported:TypeTraitExpr` | 0 | 1 | builtin-types-compatible-p.c |

## Dynamic first-refusal ranking

The run's first refusal, normalized by construct; `sole` counts rows whose first refusal is this wall.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `frontend` | 294 | 294 | 20000227-1.c, 20000412-3.c, 20000717-3.c, 20000822-1.c, 20001009-2.c |
| `undefined-behavior` | 105 | 105 | 00032.c, 00115.c, 00141.c, 00144.c, 00200.c |
| `unsupported:no definition for 'main'` | 102 | 102 | 20040705-1.c, 20040705-2.c, 20040709-3.c, builtins/20010124-1.c, builtins/abs-1.c |
| `timeout` | 66 | 66 | 00041.c, 00128.c, 20000412-2.c, 20020108-1.c, 20030916-1.c |
| `unsupported:extern object 'inside_main' has no definition in the translation unit` | 40 | 40 | builtins/20010124-1-lib.c, builtins/complex-1-lib.c, builtins/fputs-lib.c, builtins/lib/abs.c, builtins/lib/bfill.c |
| `cast:FloatingCast` | 29 | 29 | 00174.c, 00175.c, 20000605-1.c, 20020413-1.c, 920618-1.c |
| `unsupported:pointer bit-cast across incompatible effective types` | 21 | 21 | 00103.c, 20001017-2.c, 20050316-1.c, 20050607-1.c, 20060412-1.c |
| `unsequenced-effects` | 20 | 20 | 20001228-1.c, 20021120-1.c, 20050218-1.c, 20051021-1.c, 20060929-1.c |
| `unsupported:case label nested in a control statement` | 13 | 13 | 00051.c, 00143.c, 00182.c, 20011109-1.c, 20080719-1.c |
| `unsupported:integer-to-pointer conversion is not an unchanged uintptr_t/intptr_t round-trip` | 12 | 12 | 00214.c, 20000622-1.c, 20010329-1.c, 20021010-2.c, 20041112-1.c |
| `unsupported:pointer-to-integer conversion outside uintptr_t/intptr_t` | 12 | 12 | 20011121-1.c, 20060420-1.c, 941014-1.c, 980526-2.c, alloca-1.c |
| `libc-call: malloc` | 9 | 9 | 20020406-1.c, 960521-1.c, 990628-1.c, pr111613.c, pr41395-1.c |
| `unsupported:no layout for declared type 'V'` | 9 | 9 | pr105613.c, pr110817-1.c, pr110817-2.c, pr110817-3.c, pr71626-1.c |
| `unsupported:AddrLabelExpr` | 8 | 8 | 20040302-1.c, 20071210-1.c, 920302-1.c, 920501-4.c, 920501-5.c |
| `unsupported:long double floating literal` | 8 | 8 | 20030914-1.c, 20080502-1.c, gcc/testsuite/gcc.dg/c23-float-1.c, ieee/20010226-1.c, ieee/pr36332.c |
| `unsupported:va_arg requested unsupported value type 'struct tiny'` | 8 | 8 | 931004-10.c, 931004-12.c, 931004-14.c, 931004-2.c, 931004-4.c |
| `unsupported:StmtExpr` | 7 | 7 | 20000703-1.c, 20000917-1.c, 20020206-1.c, 20020320-1.c, 930406-1.c |
| `unsupported:unsupported bit-field width 1 for 'int'` | 7 | 7 | pr110165-1.c, pr110166-1.c, pr48973-1.c, pr48973-2.c, pr49123.c |
| `libc-call: __builtin_abort` | 6 | 6 | 20181120-1.c, 20230630-2.c, 20230630-4.c, gcc/testsuite/gcc.dg/c23-nullptr-5.c, pr77767.c |
| `libc-call: __builtin_malloc` | 6 | 6 | 20071018-1.c, 20071120-1.c, pr36765.c, pr43008.c, pr84339.c |
| `unsupported:DesignatedInitUpdateExpr` | 6 | 6 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-1.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-17.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-2.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-4.c |
| `unsupported:break, continue or goto escaped a function body` | 6 | 6 | 00010.c, 00199.c, 20030909-1.c, 20040704-1.c, pr119291.c |
| `unsupported:function-to-pointer decay (inch 5)` | 5 | 5 | 20021118-2.c, 20041212-1.c, 20101011-1.c, pr42231.c, pr68390.c |
| `unsupported:no layout for declared type '_Complex double'` | 5 | 5 | 20030910-1.c, 960512-1.c, complex-1.c, complex-2.c, ieee/cdivchkd.c |
| `unsupported:no layout for declared type 'struct S'` | 5 | 5 | 20050107-1.c, 20171008-1.c, pr52979-1.c, pr52979-2.c, pr79737-1.c |
| `unsupported:unbound declaration 'id180' (name 'stdout')` | 5 | 5 | 00189.c, fprintf-1.c, fprintf-chk-1.c, vfprintf-1.c, vfprintf-chk-1.c |
| `unsupported:extern object 'b' has no definition in the translation unit` | 4 | 4 | alias-2.c, alias-3.c, alias-4.c, gcc/testsuite/gcc.dg/c23-bool-2.c |
| `unsupported:indirect call through a non-FunctionDecl reference` | 4 | 4 | 20010122-1.c, pr28289.c, pr34768-1.c, pr34768-2.c |
| `unsupported:not an integer type: 'double'` | 4 | 4 | 961223-1.c, ieee/pr28634.c, pr29798.c, stdarg-4.c |
| `unsupported:string literal with escape or non-ASCII spelling` | 4 | 4 | 20010325-1.c, printf-1.c, wchar_t-1.c, widechar-3.c |
| `libc-call: __builtin_inf` | 3 | 3 | ieee/fp-cmp-7.c, ieee/inf-2.c, ieee/inf-4.c |
| `libc-call: vprintf` | 3 | 3 | printf-chk-1.c, vprintf-1.c, vprintf-chk-1.c |
| `unsupported:floating literal lacks parser-native bits` | 3 | 3 | 960513-1.c, ieee/fp-cmp-1.c, ieee/fp-cmp-2.c |
| `unsupported:implicit value initialization in value position` | 3 | 3 | pr108498-2.c, pr88739.c, pr97764.c |
| `unsupported:no layout for declared type 'A'` | 3 | 3 | 20010118-1.c, restrict-1.c, strct-pack-2.c |
| `unsupported:no layout for declared type 'T'` | 3 | 3 | 920908-1.c, 931005-1.c, pr98474.c |
| `unsupported:no layout for declared type '_Complex float'` | 3 | 3 | complex-6.c, ieee/cdivchkf.c, pr38969.c |
| `unsupported:no layout for declared type 'enum bar'` | 3 | 3 | gcc/testsuite/gcc.dg/c23-tag-alias-1.c, gcc/testsuite/gcc.dg/c23-tag-alias-2.c, gcc/testsuite/gcc.dg/c23-tag-alias-3.c |
| `unsupported:no layout for declared type 'int[n % 1000 + 1]'` | 3 | 3 | 20040811-1.c, pr43220.c, vla-dealloc-1.c |
| `unsupported:no layout for declared type 'long double'` | 3 | 3 | 20040208-1.c, ieee/20011123-1.c, ieee/pr29302-1.c |
| `unsupported:no layout for declared type 'struct S[2]'` | 3 | 3 | 20050119-1.c, 20050119-2.c, pr71700.c |
| `unsupported:no layout for field 'd'` | 3 | 3 | builtins/pr22237-1.c, builtins/pr22237.c, pr43784.c |
| `unsupported:printf` | 3 | 3 | 00195.c, 00213.c, 00215.c |
| `unsupported:sprintf` | 3 | 3 | 920501-8.c, ieee/920810-1.c, pr79327.c |
| `unsupported:type trait '__alignof'` | 3 | 3 | 20000223-1.c, align-3.c, zerolen-2.c |
| `unsupported:union initializer has no member` | 3 | 3 | pr15296.c, pr19687.c, pr23324.c |
| `unsupported:unsupported bit-field width 32 for 'unsigned long long'` | 3 | 3 | 20081117-1.c, 930126-1.c, pr65215-3.c |
| `libc-call: __builtin_copysign` | 2 | 2 | ieee/mzero6.c, pr44683.c |
| `libc-call: calloc` | 2 | 2 | 00040.c, ipa-sra-2.c |
| `libc-call: exit (an argument is not a literal 0 — which exit was reached is unknown)` | 2 | 2 | 970217-1.c, loop-8.c |
| `libc-call: floor` | 2 | 2 | 990826-0.c, float-floor.c |
| `libc-call: open` | 2 | 2 | loop-2f.c, loop-2g.c |
| `unsupported:ExprWithCleanups` | 2 | 2 | 950628-1.c, pr30185.c |
| `unsupported:GCCAsmStmt` | 2 | 2 | 20071211-1.c, pr81588.c |
| `unsupported:GenericSelectionExpr` | 2 | 2 | gcc/testsuite/gcc.dg/c23-bool-1.c, gcc/testsuite/gcc.dg/c23-float-2.c |
| `unsupported:OffsetOfExpr` | 2 | 2 | pr30778.c, pr44468.c |
| `unsupported:call to '__builtin_nanf' in a context with no program — call it through 'callByName'` | 2 | 2 | gcc/testsuite/gcc.dg/c23-float-4.c, gcc/testsuite/gcc.dg/c23-float-5.c |
| `unsupported:cannot initialize aggregate 'struct T'` | 2 | 2 | pr22141-1.c, pr22141-2.c |
| `unsupported:extern object 'abs_called' has no definition in the translation unit` | 2 | 2 | builtins/abs-1-lib.c, builtins/uabs-1-lib.c |
| `unsupported:extern object 'x' has no definition in the translation unit` | 2 | 2 | 00094.c, 00110.c |
| `unsupported:floating value used as an integer` | 2 | 2 | 20000731-1.c, 20011217-1.c |
| `unsupported:goto skips a block declaration` | 2 | 2 | 00129.c, gcc/testsuite/gcc.dg/c23-labels-1.c |
| `unsupported:long double integer-to-floating conversion` | 2 | 2 | 930622-2.c, conversion.c |
| `unsupported:more arguments than parameters` | 2 | 2 | gcc/testsuite/gcc.dg/c23-stdarg-9.c, va-arg-2.c |
| `unsupported:no layout for declared type 'U'` | 2 | 2 | 20011113-1.c, 20180131-1.c |
| `unsupported:no layout for declared type 'bitmap_iterator'` | 2 | 2 | 20090113-2.c, 20090113-3.c |
| `unsupported:no layout for declared type 'enum E'` | 2 | 2 | 00054.c, 00055.c |
| `unsupported:no layout for declared type 'int *volatile'` | 2 | 2 | 20101025-1.c, builtin-prefetch-3.c |
| `unsupported:no layout for declared type 'jmp_buf'` | 2 | 2 | 20210505-1.c, pr56982.c |
| `unsupported:no layout for declared type 'st'` | 2 | 2 | pr31448-2.c, pr31448.c |
| `unsupported:no layout for declared type 'struct c'` | 2 | 2 | 990326-1.c, packed-aligned.c |
| `unsupported:no layout for declared type 'struct foo'` | 2 | 2 | bf-pack-1.c, gcc/testsuite/gcc.dg/c23-tag-alias-7.c |
| `unsupported:no layout for declared type 'struct packed_ushort'` | 2 | 2 | 20170401-1.c, pr45070.c |
| `unsupported:no layout for declared type 'struct s'` | 2 | 2 | 20040625-1.c, pr29006.c |
| `unsupported:no layout for declared type 'struct1'` | 2 | 2 | pr86659-1.c, pr86659-2.c |
| `unsupported:no layout for declared type 'v16di'` | 2 | 2 | pr123625-2.c, pr126405-3.c |
| `unsupported:no layout for field 'b'` | 2 | 2 | pr38151.c, pr44164.c |
| `unsupported:not an integer type: 'float'` | 2 | 2 | postmod-1.c, pr15262-2.c |
| `unsupported:sizeof: no layout for operand type 'struct S'` | 2 | 2 | 20120105-1.c, pr86492.c |
| `unsupported:strlen` | 2 | 2 | 20030221-1.c, strlen-3.c |
| `unsupported:unbound declaration 'id15' (name 'a')` | 2 | 2 | gcc/testsuite/gcc.dg/c23-imaginary-constants-1.c, gcc/testsuite/gcc.dg/c23-imaginary-constants-7.c |
| `unsupported:unbound declaration 'id21' (name 'a')` | 2 | 2 | 00091.c, pr56837.c |
| `unsupported:unbound declaration 'id29' (name 'gap')` | 2 | 2 | stdarg-1.c, stdarg-2.c |
| `unsupported:unbound declaration 'id30' (name 'u')` | 2 | 2 | 20050604-1.c, 991228-1.c |
| `unsupported:unbound declaration 'id39' (name 'X')` | 2 | 2 | 960215-1.c, regstack-1.c |
| `unsupported:unsupported bit-field width 40 for 'unsigned long long'` | 2 | 2 | pr32244-1.c, pr34971.c |
| `unsupported:unsupported bit-field width 52 for 'long long'` | 2 | 2 | 991118-1.c, bf64-1.c |
| `cast:FloatingComplexCast` | 1 | 1 | 20070614-1.c |
| `cast:FloatingRealToComplex` | 1 | 1 | complex-4.c |
| `cast:IntegralComplexCast` | 1 | 1 | 20041124-1.c |
| `cast:IntegralRealToComplex` | 1 | 1 | pr104604.c |
| `libc-call: __builtin_classify_type` | 1 | 1 | 20040709-1.c |
| `libc-call: __builtin_constant_p` | 1 | 1 | builtin-constant.c |
| `libc-call: __builtin_frame_address` | 1 | 1 | frame-address.c |
| `libc-call: __builtin_huge_val` | 1 | 1 | ieee/inf-3.c |
| `libc-call: __builtin_inff` | 1 | 1 | ieee/inf-1.c |
| `libc-call: __builtin_isinf` | 1 | 1 | ieee/pr108540-1.c |
| `libc-call: __builtin_isunordered` | 1 | 1 | ieee/compare-fp-3.c |
| `libc-call: __builtin_nanf` | 1 | 1 | ieee/pr119002.c |
| `libc-call: __builtin_setjmp` | 1 | 1 | built-in-setjmp.c |
| `libc-call: __builtin_signbit` | 1 | 1 | pr35456.c |
| `libc-call: __builtin_snprintf` | 1 | 1 | pr78622.c |
| `libc-call: f` | 1 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: fabs` | 1 | 1 | 20020720-1.c |
| `libc-call: fopen` | 1 | 1 | 00187.c |
| `libc-call: main_test` | 1 | 1 | builtins/lib/main.c |
| `libc-call: mempcpy` | 1 | 1 | string-opt-18.c |
| `libc-call: pow` | 1 | 1 | 980709-1.c |
| `libc-call: sin` | 1 | 1 | ieee/mzero4.c |
| `unsupported:AlignedAttr` | 1 | 1 | pr108064.c |
| `unsupported:IndirectGotoStmt` | 1 | 1 | 920501-3.c |
| `unsupported:TypeTraitExpr` | 1 | 1 | builtin-types-compatible-p.c |
| `unsupported:block-scope storage class 'extern' is outside the tier` | 1 | 1 | scope-1.c |
| `unsupported:call through an incompatible function-pointer cast` | 1 | 1 | call-trap-1.c |
| `unsupported:call to '__builtin_inff' in a context with no program — call it through 'callByName'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-float-3.c |
| `unsupported:call to '__builtin_nan' in a context with no program — call it through 'callByName'` | 1 | 1 | ieee/builtin-nan-1.c |
| `unsupported:cannot initialize aggregate 'int'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-empty-init-1.c |
| `unsupported:cannot initialize aggregate 'struct D'` | 1 | 1 | pr39339.c |
| `unsupported:cannot initialize aggregate 'u8'` | 1 | 1 | 00216.c |
| `unsupported:compound literal initializer callback unavailable` | 1 | 1 | 20050929-1.c |
| `unsupported:explicit initializer for flexible array member 'j'` | 1 | 1 | pr33382.c |
| `unsupported:explicit initializer for flexible array member 'z'` | 1 | 1 | 20030109-1.c |
| `unsupported:extern object 'ReadyFlag_NotProperlyInitialized' has no definition in the translation unit` | 1 | 1 | pr31072.c |
| `unsupported:extern object 'aa' has no definition in the translation unit` | 1 | 1 | 20000403-1.c |
| `unsupported:extern object 'i' has no definition in the translation unit` | 1 | 1 | pure-1.c |
| `unsupported:extern object 'p' has no definition in the translation unit` | 1 | 1 | gcc/testsuite/gcc.dg/c23-unreachable-1.c |
| `unsupported:function instrumentation is outside the tier` | 1 | 1 | eeprof-1.c |
| `unsupported:initializer list (inch 4)` | 1 | 1 | 00150.c |
| `unsupported:memcmp` | 1 | 1 | 20050502-2.c |
| `unsupported:no layout for compound literal type 'T'` | 1 | 1 | 20071029-1.c |
| `unsupported:no layout for compound literal type 'V'` | 1 | 1 | pr109040.c |
| `unsupported:no layout for declared type 'A0'` | 1 | 1 | va-arg-22.c |
| `unsupported:no layout for declared type 'DB_TXNLIST'` | 1 | 1 | 20011008-3.c |
| `unsupported:no layout for declared type 'PgHdr[5]'` | 1 | 1 | pr33870-1.c |
| `unsupported:no layout for declared type 'Point'` | 1 | 1 | 20000808-1.c |
| `unsupported:no layout for declared type 'Q'` | 1 | 1 | simd-5.c |
| `unsupported:no layout for declared type 'ScanfState'` | 1 | 1 | va-arg-13.c |
| `unsupported:no layout for declared type 'T0 *const'` | 1 | 1 | 991016-1.c |
| `unsupported:no layout for declared type 'TRIAL'` | 1 | 1 | strct-pack-1.c |
| `unsupported:no layout for declared type 'V2SF'` | 1 | 1 | 20050316-2.c |
| `unsupported:no layout for declared type 'V32'` | 1 | 1 | pr70903.c |
| `unsupported:no layout for declared type 'V[32]'` | 1 | 1 | ieee/pr72824-2.c |
| `unsupported:no layout for declared type 'X'` | 1 | 1 | struct-ret-1.c |
| `unsupported:no layout for declared type '_Complex double[12]'` | 1 | 1 | pr49644.c |
| `unsupported:no layout for declared type '_Complex double[1]'` | 1 | 1 | 20020411-1.c |
| `unsupported:no layout for declared type '_Complex long double'` | 1 | 1 | ieee/cdivchkld.c |
| `unsupported:no layout for declared type '__attribute__((__vector_size__(16 * sizeof(char)))) char'` | 1 | 1 | scal-to-vec2.c |
| `unsupported:no layout for declared type '__attribute__((__vector_size__(4 * sizeof(float)))) float'` | 1 | 1 | scal-to-vec3.c |
| `unsupported:no layout for declared type '__attribute__((__vector_size__(8 * sizeof(short)))) short'` | 1 | 1 | scal-to-vec1.c |
| `unsupported:no layout for declared type '__m128i'` | 1 | 1 | pr92618.c |
| `unsupported:no layout for declared type 'a_struct'` | 1 | 1 | 960608-1.c |
| `unsupported:no layout for declared type 'aun'` | 1 | 1 | pr19515.c |
| `unsupported:no layout for declared type 'big'` | 1 | 1 | va-arg-4.c |
| `unsupported:no layout for declared type 'big_t'` | 1 | 1 | pr23135.c |
| `unsupported:no layout for declared type 'bu'` | 1 | 1 | 921204-1.c |
| `unsupported:no layout for declared type 'char *volatile'` | 1 | 1 | pr36321.c |
| `unsupported:no layout for declared type 'char[argc]'` | 1 | 1 | 00207.c |
| `unsupported:no layout for declared type 'client_t'` | 1 | 1 | 20071030-1.c |
| `unsupported:no layout for declared type 'const A3_28 *const'` | 1 | 1 | strlen-4.c |
| `unsupported:no layout for declared type 'const char *const'` | 1 | 1 | string-opt-5.c |
| `unsupported:no layout for declared type 'const char *const[1]'` | 1 | 1 | pr53084.c |
| `unsupported:no layout for declared type 'const gs_imager_state'` | 1 | 1 | 20080117-1.c |
| `unsupported:no layout for declared type 'const int *const'` | 1 | 1 | 00219.c |
| `unsupported:no layout for declared type 'const struct try[6]'` | 1 | 1 | ieee/fp-cmp-4.c |
| `unsupported:no layout for declared type 'double (*)()'` | 1 | 1 | 930608-1.c |
| `unsupported:no layout for declared type 'double (*)(float)'` | 1 | 1 | func-ptr-1.c |
| `unsupported:no layout for declared type 'double[n]'` | 1 | 1 | 920929-1.c |
| `unsupported:no layout for declared type 'enum e'` | 1 | 1 | enum-3.c |
| `unsupported:no layout for declared type 'enum fred'` | 1 | 1 | 00170.c |
| `unsupported:no layout for declared type 'gfc_array_i4'` | 1 | 1 | 20090113-1.c |
| `unsupported:no layout for declared type 'hexdouble'` | 1 | 1 | ieee/unsafe-fp-assoc-1.c |
| `unsupported:no layout for declared type 'info_t'` | 1 | 1 | 20100430-1.c |
| `unsupported:no layout for declared type 'int (*(*)(int, int))(int, int)'` | 1 | 1 | 00124.c |
| `unsupported:no layout for declared type 'int (*)(int, int)'` | 1 | 1 | 991112-1.c |
| `unsupported:no layout for declared type 'int (*)[++i]'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-auto-2.c |
| `unsupported:no layout for declared type 'int ***volatile'` | 1 | 1 | pr58277-2.c |
| `unsupported:no layout for declared type 'int32_t'` | 1 | 1 | 00104.c |
| `unsupported:no layout for declared type 'int[len][len]'` | 1 | 1 | 20221006-1.c |
| `unsupported:no layout for declared type 'io'` | 1 | 1 | 20031201-1.c |
| `unsupported:no layout for declared type 'mp_int'` | 1 | 1 | 20180226-1.c |
| `unsupported:no layout for declared type 'neon_s8'` | 1 | 1 | pr42833.c |
| `unsupported:no layout for declared type 's'` | 1 | 1 | 00046.c |
| `unsupported:no layout for declared type 'spinlock_t'` | 1 | 1 | zero-struct-2.c |
| `unsupported:no layout for declared type 'struc'` | 1 | 1 | 20001101.c |
| `unsupported:no layout for declared type 'struct A'` | 1 | 1 | 20040709-2.c |
| `unsupported:no layout for declared type 'struct S[21]'` | 1 | 1 | pr70602.c |
| `unsupported:no layout for declared type 'struct S[6]'` | 1 | 1 | pr58570.c |
| `unsupported:no layout for declared type 'struct bar'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-tag-alias-4.c |
| `unsupported:no layout for declared type 'struct brfic_args'` | 1 | 1 | 20001026-1.c |
| `unsupported:no layout for declared type 'struct event'` | 1 | 1 | 20111212-1.c |
| `unsupported:no layout for declared type 'struct printf_spec'` | 1 | 1 | 20190820-1.c |
| `unsupported:no layout for declared type 'struct product_iSfd_'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-tag-5.c |
| `unsupported:no layout for declared type 'struct tty_driver'` | 1 | 1 | struct-cpy-1.c |
| `unsupported:no layout for declared type 'struct write_data'` | 1 | 1 | 20000815-1.c |
| `unsupported:no layout for declared type 'struct x'` | 1 | 1 | 20020227-1.c |
| `unsupported:no layout for declared type 'struct_list'` | 1 | 1 | 921113-1.c |
| `unsupported:no layout for declared type 't'` | 1 | 1 | 920810-1.c |
| `unsupported:no layout for declared type 't_be'` | 1 | 1 | 960416-1.c |
| `unsupported:no layout for declared type 'three_byte_t'` | 1 | 1 | struct-ret-2.c |
| `unsupported:no layout for declared type 'three_char_t'` | 1 | 1 | strct-pack-4.c |
| `unsupported:no layout for declared type 'token'` | 1 | 1 | enum-1.c |
| `unsupported:no layout for declared type 'uint32_t'` | 1 | 1 | 20120111-1.c |
| `unsupported:no layout for declared type 'uint32_t[16]'` | 1 | 1 | pr65369.c |
| `unsupported:no layout for declared type 'unit_flags'` | 1 | 1 | 20090527-1.c |
| `unsupported:no layout for declared type 'v4qi'` | 1 | 1 | pr60960.c |
| `unsupported:no layout for declared type 'v8qi'` | 1 | 1 | simd-6.c |
| `unsupported:no layout for declared type 'void *volatile'` | 1 | 1 | pr84521.c |
| `unsupported:no layout for declared type 'volatile a_struct'` | 1 | 1 | 20010518-2.c |
| `unsupported:no layout for declared type 'volatile enum X'` | 1 | 1 | 20030903-1.c |
| `unsupported:no layout for declared type 'volatile long double'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-float-12.c |
| `unsupported:no layout for declared type 'wchar_t[21]'` | 1 | 1 | 00220.c |
| `unsupported:no layout for field 'c'` | 1 | 1 | pr47538.c |
| `unsupported:no layout for field 'code'` | 1 | 1 | 00218.c |
| `unsupported:no layout for field 'f2'` | 1 | 1 | pr101188.c |
| `unsupported:no layout for field 'fptr'` | 1 | 1 | 00087.c |
| `unsupported:no layout for field 'j'` | 1 | 1 | pr97073.c |
| `unsupported:no layout for field 'n'` | 1 | 1 | pr39100.c |
| `unsupported:no layout for field 's'` | 1 | 1 | 20190901-1.c |
| `unsupported:no layout for field 'y'` | 1 | 1 | 00053.c |
| `unsupported:no layout for parameter type 'const unsigned int *const'` | 1 | 1 | pr63209.c |
| `unsupported:no layout for parameter type 'foo_t *const'` | 1 | 1 | pr33669.c |
| `unsupported:no layout for parameter type 'int **restrict'` | 1 | 1 | 20080506-2.c |
| `unsupported:no layout for parameter type 'int *restrict'` | 1 | 1 | pr38212.c |
| `unsupported:no size for pointee of 'int (*)[4]'` | 1 | 1 | pr124358.c |
| `unsupported:non-object declaration in a block` | 1 | 1 | 00078.c |
| `unsupported:not an integer type: 'T'` | 1 | 1 | pr84169.c |
| `unsupported:not an lvalue: PredefinedExpr` | 1 | 1 | 20001011-1.c |
| `unsupported:operator '-' on pointers from different arrays` | 1 | 1 | 950710-1.c |
| `unsupported:operator '-' on pointers without array provenance` | 1 | 1 | 980701-1.c |
| `unsupported:sizeof: no layout for operand type 'PT[9]'` | 1 | 1 | 00205.c |
| `unsupported:sizeof: no layout for operand type 'Union'` | 1 | 1 | 20051113-1.c |
| `unsupported:sizeof: no layout for operand type '_Atomic(unsigned char)'` | 1 | 1 | gcc/testsuite/gcc.dg/atomic/c23-stdatomic-lockfree-char8_t.c |
| `unsupported:sizeof: no layout for operand type 'c'` | 1 | 1 | 20040411-1.c |
| `unsupported:sizeof: no layout for operand type 'foo_t'` | 1 | 1 | 941014-2.c |
| `unsupported:sizeof: no layout for operand type 'int (*volatile[6])(void)'` | 1 | 1 | bcp-1.c |
| `unsupported:sizeof: no layout for operand type 'struct tree_common'` | 1 | 1 | 20000914-1.c |
| `unsupported:sizeof: no layout for operand type 'va_list'` | 1 | 1 | va-arg-21.c |
| `unsupported:src/20000412-5.c` | 1 | 1 | 20000412-5.c |
| `unsupported:src/20040307-1.c` | 1 | 1 | 20040307-1.c |
| `unsupported:src/20040331-1.c` | 1 | 1 | 20040331-1.c |
| `unsupported:src/20050316-3.c` | 1 | 1 | 20050316-3.c |
| `unsupported:src/921016-1.c` | 1 | 1 | 921016-1.c |
| `unsupported:src/930628-1.c` | 1 | 1 | 930628-1.c |
| `unsupported:src/bf-layout-1.c` | 1 | 1 | bf-layout-1.c |
| `unsupported:src/bf-sign-1.c` | 1 | 1 | bf-sign-1.c |
| `unsupported:src/cbrt.c` | 1 | 1 | cbrt.c |
| `unsupported:src/ffs-2.c` | 1 | 1 | ffs-2.c |
| `unsupported:src/ieee/mul-subnormal-single-1.c` | 1 | 1 | ieee/mul-subnormal-single-1.c |
| `unsupported:src/memcpy-2.c` | 1 | 1 | memcpy-2.c |
| `unsupported:src/memset-1.c` | 1 | 1 | memset-1.c |
| `unsupported:src/memset-2.c` | 1 | 1 | memset-2.c |
| `unsupported:src/memset-3.c` | 1 | 1 | memset-3.c |
| `unsupported:src/pr33631.c` | 1 | 1 | pr33631.c |
| `unsupported:src/pr49768.c` | 1 | 1 | pr49768.c |
| `unsupported:src/simd-4.c` | 1 | 1 | simd-4.c |
| `unsupported:src/strcmp-1.c` | 1 | 1 | strcmp-1.c |
| `unsupported:src/strcpy-1.c` | 1 | 1 | strcpy-1.c |
| `unsupported:src/strlen-1.c` | 1 | 1 | strlen-1.c |
| `unsupported:src/strlen-5.c` | 1 | 1 | strlen-5.c |
| `unsupported:src/strncmp-1.c` | 1 | 1 | strncmp-1.c |
| `unsupported:strcmp` | 1 | 1 | p18298.c |
| `unsupported:unary operator '__real'` | 1 | 1 | 20050121-1.c |
| `unsupported:unbound declaration 'id103' (name 'test')` | 1 | 1 | pr71083.c |
| `unsupported:unbound declaration 'id15' (name 'extfunc')` | 1 | 1 | pr67037.c |
| `unsupported:unbound declaration 'id15' (name 'f1')` | 1 | 1 | complex-7.c |
| `unsupported:unbound declaration 'id15' (name 'fptr')` | 1 | 1 | 00088.c |
| `unsupported:unbound declaration 'id15' (name 'x')` | 1 | 1 | 20090623-1.c |
| `unsupported:unbound declaration 'id15' (name 'zero')` | 1 | 1 | 00089.c |
| `unsupported:unbound declaration 'id151' (name 's')` | 1 | 1 | pr91597.c |
| `unsupported:unbound declaration 'id18' (name 'a')` | 1 | 1 | pr65427.c |
| `unsupported:unbound declaration 'id18' (name 'g')` | 1 | 1 | 20031214-1.c |
| `unsupported:unbound declaration 'id18' (name 's')` | 1 | 1 | 20051104-1.c |
| `unsupported:unbound declaration 'id185' (name 'w')` | 1 | 1 | pr47337.c |
| `unsupported:unbound declaration 'id19' (name 'b')` | 1 | 1 | bitfld-signed1-1.c |
| `unsupported:unbound declaration 'id19' (name 'c')` | 1 | 1 | pr97421-1.c |
| `unsupported:unbound declaration 'id19' (name 'f')` | 1 | 1 | signed1bitfield-1.c |
| `unsupported:unbound declaration 'id19' (name 's')` | 1 | 1 | 00047.c |
| `unsupported:unbound declaration 'id20' (name 'a')` | 1 | 1 | pr70127.c |
| `unsupported:unbound declaration 'id21' (name 'g1s')` | 1 | 1 | pr42248.c |
| `unsupported:unbound declaration 'id21' (name 's')` | 1 | 1 | 20041201-1.c |
| `unsupported:unbound declaration 'id21' (name 'v')` | 1 | 1 | 00024.c |
| `unsupported:unbound declaration 'id22' (name 'b')` | 1 | 1 | pr58726.c |
| `unsupported:unbound declaration 'id22' (name 'c')` | 1 | 1 | pr103417.c |
| `unsupported:unbound declaration 'id22' (name 's')` | 1 | 1 | pr67781.c |
| `unsupported:unbound declaration 'id22' (name 't')` | 1 | 1 | packed-2.c |
| `unsupported:unbound declaration 'id25' (name 'f')` | 1 | 1 | pr19689.c |
| `unsupported:unbound declaration 'id25' (name 'v')` | 1 | 1 | 20050215-1.c |
| `unsupported:unbound declaration 'id26' (name 'u')` | 1 | 1 | pr87053.c |
| `unsupported:unbound declaration 'id27' (name 'a')` | 1 | 1 | 20031215-1.c |
| `unsupported:unbound declaration 'id27' (name 'f')` | 1 | 1 | 921208-1.c |
| `unsupported:unbound declaration 'id27' (name 'x')` | 1 | 1 | 960405-1.c |
| `unsupported:unbound declaration 'id28' (name 'arr')` | 1 | 1 | pr55750.c |
| `unsupported:unbound declaration 'id28' (name 'cp')` | 1 | 1 | 20120808-1.c |
| `unsupported:unbound declaration 'id28' (name 'terminate_me')` | 1 | 1 | pr54937.c |
| `unsupported:unbound declaration 'id28' (name 'v')` | 1 | 1 | 00050.c |
| `unsupported:unbound declaration 'id29' (name 't')` | 1 | 1 | 20051012-1.c |
| `unsupported:unbound declaration 'id30' (name 'b')` | 1 | 1 | 20131127-1.c |
| `unsupported:unbound declaration 'id30' (name 'f')` | 1 | 1 | pr98366.c |
| `unsupported:unbound declaration 'id30' (name 'x')` | 1 | 1 | 20011019-1.c |
| `unsupported:unbound declaration 'id31' (name 'ap')` | 1 | 1 | va-arg-trap-1.c |
| `unsupported:unbound declaration 'id31' (name 'global')` | 1 | 1 | va-arg-14.c |
| `unsupported:unbound declaration 'id31' (name 't')` | 1 | 1 | 980602-2.c |
| `unsupported:unbound declaration 'id31' (name 'wordlist')` | 1 | 1 | 20000412-1.c |
| `unsupported:unbound declaration 'id32' (name 'foo')` | 1 | 1 | anon-1.c |
| `unsupported:unbound declaration 'id32' (name 'node')` | 1 | 1 | 20030224-2.c |
| `unsupported:unbound declaration 'id33' (name 't')` | 1 | 1 | packed-1.c |
| `unsupported:unbound declaration 'id33' (name 'x')` | 1 | 1 | 921112-1.c |
| `unsupported:unbound declaration 'id339' (name 'g_this')` | 1 | 1 | 20030714-1.c |
| `unsupported:unbound declaration 'id36' (name 'actual_function')` | 1 | 1 | 00210.c |
| `unsupported:unbound declaration 'id36' (name 's')` | 1 | 1 | 930408-1.c |
| `unsupported:unbound declaration 'id37' (name 'b')` | 1 | 1 | 20040629-1.c |
| `unsupported:unbound declaration 'id37' (name 'pts')` | 1 | 1 | 920625-1.c |
| `unsupported:unbound declaration 'id37' (name 'x')` | 1 | 1 | 931110-1.c |
| `unsupported:unbound declaration 'id38' (name 's')` | 1 | 1 | 20000801-3.c |
| `unsupported:unbound declaration 'id40' (name 'x')` | 1 | 1 | struct-ini-2.c |
| `unsupported:unbound declaration 'id42' (name 'y')` | 1 | 1 | 20010904-1.c |
| `unsupported:unbound declaration 'id426' (name 'array')` | 1 | 1 | pr34456.c |
| `unsupported:unbound declaration 'id43' (name 'buf')` | 1 | 1 | pr93908.c |
| `unsupported:unbound declaration 'id43' (name 'y')` | 1 | 1 | 20010904-2.c |
| `unsupported:unbound declaration 'id45' (name 'k')` | 1 | 1 | simd-1.c |
| `unsupported:unbound declaration 'id48' (name 'curval')` | 1 | 1 | 960117-1.c |
| `unsupported:unbound declaration 'id487' (name 'MyPte')` | 1 | 1 | 20020402-2.c |
| `unsupported:unbound declaration 'id49' (name 'result')` | 1 | 1 | struct-ini-3.c |
| `unsupported:unbound declaration 'id50' (name 'ws')` | 1 | 1 | widechar-2.c |
| `unsupported:unbound declaration 'id561' (name 'b')` | 1 | 1 | pr103209.c |
| `unsupported:unbound declaration 'id66' (name 'k')` | 1 | 1 | simd-2.c |
| `unsupported:unbound declaration 'id67' (name 'z')` | 1 | 1 | complex-5.c |
| `unsupported:unbound declaration 'id74' (name 'p')` | 1 | 1 | pr64242.c |
| `unsupported:unknown enum declaration 'id17' (name 'X')` | 1 | 1 | 00120.c |
| `unsupported:unknown enum declaration 'id27' (name 'read')` | 1 | 1 | builtin-prefetch-1.c |
| `unsupported:unknown enum declaration 'id29' (name 'BAR')` | 1 | 1 | enum-2.c |
| `unsupported:unknown enum declaration 'id41' (name 'N')` | 1 | 1 | 20011219-1.c |
| `unsupported:unknown enum declaration 'id513' (name 'a')` | 1 | 1 | 00198.c |
| `unsupported:unnamed pointer parameter (array-bound effects are not retained by clang)` | 1 | 1 | gcc/testsuite/gcc.dg/c23-parm-omit-3.c |
| `unsupported:unsupported bit-field width 12 for 'int'` | 1 | 1 | bitfld-4.c |
| `unsupported:unsupported bit-field width 2 for 'int'` | 1 | 1 | pr78170.c |
| `unsupported:unsupported bit-field width 30 for 'int'` | 1 | 1 | pr38422.c |
| `unsupported:unsupported bit-field width 31 for 'long'` | 1 | 1 | bf-sign-2.c |
| `unsupported:unsupported bit-field width 33 for 'unsigned long long'` | 1 | 1 | bitfld-3.c |
| `unsupported:unsupported bit-field width 4 for 'const int'` | 1 | 1 | pr100453.c |
| `unsupported:unsupported bit-field width 48 for 'unsigned long long'` | 1 | 1 | pr65215-4.c |
| `unsupported:unsupported bit-field width 5 for 'int'` | 1 | 1 | pr58984.c |
| `unsupported:unsupported bit-field width 7 for 'int'` | 1 | 1 | bitfld-1.c |
| `unsupported:unsupported bit-field width 8 for 'signed char'` | 1 | 1 | pr78436.c |
| `unsupported:va_arg requested unsupported value type 'struct S'` | 1 | 1 | pr92904.c |
| `unsupported:va_arg requested unsupported value type 'struct S1'` | 1 | 1 | stdarg-3.c |
| `unsupported:va_arg requested unsupported value type 'struct s'` | 1 | 1 | strct-varg-1.c |
