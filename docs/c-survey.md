# C torture survey

Generated from the pinned `C1-C3 (gcc torture, c-testsuite, gcc c23-run)` manifest.

- verdicts: 834/2214 MATCH (passed 834, failed 0, oracle 0)
- manifest SHA-256: `7c37aac5bda12272a4bb8978a53d85ad68cbc61fa13d32218d7bbf84bfbcaed7`
- measured commit: `506490cfb`
- measured at: `2026-11-12T18:11:39Z`

## Verdict counts

| verdict | files |
| --- | ---: |
| `not-parsed` | 294 |
| `oracle-tests-compiler` | 1 |
| `passed` | 834 |
| `refused-libc` | 51 |
| `refused-ub` | 65 |
| `refused-unsupported` | 918 |
| `timeout` | 51 |

## Counts by corpus

| corpus | verdict | files |
| --- | --- | ---: |
| `c-testsuite/single-exec` | `passed` | 155 |
| `c-testsuite/single-exec` | `refused-libc` | 5 |
| `c-testsuite/single-exec` | `refused-ub` | 7 |
| `c-testsuite/single-exec` | `refused-unsupported` | 51 |
| `c-testsuite/single-exec` | `timeout` | 2 |
| `gcc.c-torture/execute` | `not-parsed` | 267 |
| `gcc.c-torture/execute` | `oracle-tests-compiler` | 1 |
| `gcc.c-torture/execute` | `passed` | 677 |
| `gcc.c-torture/execute` | `refused-libc` | 44 |
| `gcc.c-torture/execute` | `refused-ub` | 57 |
| `gcc.c-torture/execute` | `refused-unsupported` | 823 |
| `gcc.c-torture/execute` | `timeout` | 49 |
| `gcc.c23-run` | `not-parsed` | 27 |
| `gcc.c23-run` | `passed` | 2 |
| `gcc.c23-run` | `refused-libc` | 2 |
| `gcc.c23-run` | `refused-ub` | 1 |
| `gcc.c23-run` | `refused-unsupported` | 44 |

## Static wall ranking

`sole` counts files whose only static wall is the named wall; `present` counts all files containing it.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `type-layout` | 366 | 1100 | 00015.c, 00016.c, 00017.c, 00018.c, 00019.c |
| `libc-call` | 215 | 758 | 00025.c, 00040.c, 00056.c, 00087.c, 00089.c |
| `cast:IntegralToPointer` | 3 | 29 | 00214.c, 20000314-1.c, 20000622-1.c, 20001101.c, 20010329-1.c |
| `unsequenced-effects` | 3 | 20 | 00121.c, 20001228-1.c, 20020406-1.c, 20060102-1.c, 20230802-1.c |
| `cast:PointerToIntegral` | 2 | 28 | 00144.c, 20000622-1.c, 20011121-1.c, 20030811-1.c, 20050215-1.c |
| `unsupported:AddrLabelExpr` | 1 | 10 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920302-1.c, 920501-4.c |
| `unsupported:StmtExpr` | 1 | 10 | 00213.c, 00214.c, 20000703-1.c, 20000917-1.c, 20001203-2.c |
| `string-literal` | 0 | 270 | 00025.c, 00026.c, 00056.c, 00058.c, 00112.c |
| `cast:IntegralToFloating` | 0 | 84 | 00113.c, 00119.c, 00123.c, 00174.c, 00175.c |
| `unsupported:VAArgExpr` | 0 | 58 | 00204.c, 20000519-1.c, 20041113-1.c, 20041214-1.c, 20071213-1.c |
| `cast:FloatingCast` | 0 | 56 | 00174.c, 00175.c, 00204.c, 20000605-1.c, 20020411-1.c |
| `cast:FloatingToIntegral` | 0 | 28 | 00175.c, 20000605-1.c, 20010118-1.c, 20031003-1.c, 20040709-1.c |
| `unsupported:PackedAttr` | 0 | 27 | 00210.c, 20010518-2.c, 20020227-1.c, 20030224-2.c, 20040625-1.c |
| `unsupported:AlignedAttr` | 0 | 15 | 20010904-1.c, 20010904-2.c, 20171008-1.c, 960117-1.c, 990326-1.c |
| `unsupported:ImaginaryLiteral` | 0 | 13 | 20041124-1.c, 20041201-1.c, 20070614-1.c, builtins/complex-1.c, complex-1.c |
| `unsupported:IndirectGotoStmt` | 0 | 10 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920302-1.c, 920501-3.c |
| `unsupported:IndirectFieldDecl` | 0 | 7 | 00046.c, 00050.c, 00216.c, 20030714-1.c, anon-1.c |
| `unsupported:DesignatedInitUpdateExpr` | 0 | 6 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-1.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-17.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-2.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-4.c |
| `unsupported:ExprWithCleanups` | 0 | 6 | 00204.c, 20020320-1.c, 20041124-1.c, 950628-1.c, gcc/testsuite/gcc.dg/c23-stdarg-9.c |
| `unsupported:GenericSelectionExpr` | 0 | 6 | 00219.c, gcc/testsuite/gcc.dg/c23-bool-1.c, gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-float-2.c, gcc/testsuite/gcc.dg/c23-float-3.c |
| `unsupported:GCCAsmStmt` | 0 | 4 | 20071211-1.c, 990413-2.c, pr56982.c, pr81588.c |
| `unsupported:OffsetOfExpr` | 0 | 4 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, pr103255.c, pr30778.c, pr44468.c |
| `unsupported:MaxFieldAlignmentAttr` | 0 | 3 | 20131127-1.c, pr58570.c, pr79737-1.c |
| `unsupported:MayAliasAttr` | 0 | 3 | mayalias-2.c, mayalias-3.c, pr43987.c |
| `unsupported:ModeAttr` | 0 | 3 | 20050107-1.c, 20050119-1.c, 20050119-2.c |
| `unsupported:PredefinedExpr` | 0 | 2 | 20001011-1.c, pr58831.c |
| `unsupported:StaticAssertDecl` | 0 | 2 | gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-digit-separators-1.c |
| `unsupported:BinaryConditionalOperator` | 0 | 1 | pr68249.c |
| `unsupported:CXXNullPtrLiteralExpr` | 0 | 1 | gcc/testsuite/gcc.dg/c23-nullptr-5.c |
| `unsupported:LabelDecl` | 0 | 1 | 980526-1.c |
| `unsupported:TypeTraitExpr` | 0 | 1 | builtin-types-compatible-p.c |

## Dynamic first-refusal ranking

The run's first refusal, normalized by construct; `sole` counts rows whose first refusal is this wall.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `frontend` | 294 | 294 | 20000227-1.c, 20000412-3.c, 20000717-3.c, 20000822-1.c, 20001009-2.c |
| `unsupported:no definition for 'main'` | 102 | 102 | 20040705-1.c, 20040705-2.c, 20040709-3.c, builtins/20010124-1.c, builtins/abs-1.c |
| `undefined-behavior` | 65 | 65 | 00115.c, 00141.c, 00144.c, 00200.c, 00204.c |
| `timeout` | 51 | 51 | 00041.c, 00128.c, 20000412-2.c, 20020108-1.c, 20030916-1.c |
| `unsupported:extern object 'inside_main' has no definition in the translation unit` | 40 | 40 | builtins/20010124-1-lib.c, builtins/complex-1-lib.c, builtins/fputs-lib.c, builtins/lib/abs.c, builtins/lib/bfill.c |
| `unsupported:pointer used as an integer (no ptr↔int cast in tier)` | 38 | 38 | 00032.c, 00173.c, 00182.c, 20000412-6.c, 20000801-1.c |
| `unsupported:more arguments than parameters` | 37 | 37 | 20000519-1.c, 20071213-1.c, 920726-1.c, 931004-10.c, 931004-12.c |
| `unsequenced-effects` | 28 | 28 | 00121.c, 20001228-1.c, 20051021-1.c, 20060102-1.c, 20060929-1.c |
| `unsupported:no layout for declared type 'double'` | 27 | 27 | 00178.c, 20000731-1.c, 20011217-1.c, 20040831-1.c, 20190901-1.c |
| `unsupported:declaration outside a block` | 26 | 26 | 20230802-1.c, alias-access-path-2.c, bitops-1.c, bswap-3.c, minmaxcmp-1.c |
| `unsupported:pointer bit-cast across incompatible effective types` | 23 | 23 | 00103.c, 20001017-2.c, 20050316-1.c, 20050607-1.c, 20060412-1.c |
| `unsupported:no layout for declared type 'struct S'` | 22 | 22 | 00087.c, 20050107-1.c, 20081103-1.c, 20100708-1.c, 20171008-1.c |
| `unsupported:no layout for parameter type 'double'` | 14 | 14 | 20020720-1.c, 920501-8.c, 941021-1.c, 980205.c, 980605-1.c |
| `cast:PointerToIntegral` | 13 | 13 | 20011121-1.c, 941014-1.c, 980526-2.c, alloca-1.c, loop-2c.c |
| `cast:IntegralToPointer` | 12 | 12 | 20000622-1.c, 20010329-1.c, 20021010-2.c, 20041112-1.c, 20050125-1.c |
| `unsupported:case label nested in a control statement` | 10 | 10 | 00051.c, 00143.c, 20011109-1.c, 20080719-1.c, 920506-1.c |
| `unsupported:no layout for declared type 'V'` | 9 | 9 | pr105613.c, pr110817-1.c, pr110817-2.c, pr110817-3.c, pr71626-1.c |
| `unsupported:no layout for declared type 'float'` | 9 | 9 | 00113.c, 00174.c, 20050121-1.c, ieee/920518-1.c, ieee/980619-1.c |
| `unsupported:AddrLabelExpr` | 8 | 8 | 20040302-1.c, 20071210-1.c, 920302-1.c, 920501-4.c, 920501-5.c |
| `unsupported:long double floating literal` | 8 | 8 | 20030914-1.c, 20080502-1.c, 960513-1.c, gcc/testsuite/gcc.dg/c23-float-1.c, ieee/20010226-1.c |
| `libc-call: malloc` | 7 | 7 | 20020406-1.c, 960521-1.c, 990628-1.c, pr41395-1.c, pr41463.c |
| `unsupported:no layout for declared type 'struct s'` | 7 | 7 | 00043.c, 20040625-1.c, 930126-1.c, 961223-1.c, pr110165-1.c |
| `unsupported:no layout for declared type 'va_list'` | 7 | 7 | printf-chk-1.c, stdarg-1.c, va-arg-14.c, vfprintf-1.c, vfprintf-chk-1.c |
| `unsupported:no layout for parameter type 'float'` | 7 | 7 | 20020321-1.c, 20080529-1.c, conversion.c, gofast.c, ieee/compare-fp-3.c |
| `cast:ToVoid` | 6 | 6 | 00212.c, 00213.c, gcc/testsuite/gcc.dg/c23-float-2.c, gcc/testsuite/gcc.dg/c23-float-3.c, gcc/testsuite/gcc.dg/c23-float-4.c |
| `libc-call: strcpy` | 6 | 6 | 00179.c, 00180.c, 20120207-1.c, 980707-1.c, built-in-setjmp.c |
| `unsupported:DesignatedInitUpdateExpr` | 6 | 6 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-1.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-17.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-2.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-4.c |
| `unsupported:StmtExpr` | 6 | 6 | 20000703-1.c, 20000917-1.c, 20020206-1.c, 20020320-1.c, 930406-1.c |
| `unsupported:break, continue or goto escaped a function body` | 6 | 6 | 00010.c, 00199.c, 20030909-1.c, 20040704-1.c, pr119291.c |
| `libc-call: __builtin_malloc` | 5 | 5 | 20071018-1.c, 20071120-1.c, pr36765.c, pr43008.c, pr84339.c |
| `unsupported:indirect call through a non-FunctionDecl reference` | 5 | 5 | 00089.c, 20010122-1.c, pr28289.c, pr34768-1.c, pr34768-2.c |
| `unsupported:no layout for declared type '_Complex double'` | 5 | 5 | 20030910-1.c, 960512-1.c, complex-1.c, complex-2.c, ieee/cdivchkd.c |
| `unsupported:string literal with escape or non-ASCII spelling` | 5 | 5 | 00175.c, 20010325-1.c, printf-1.c, wchar_t-1.c, widechar-3.c |
| `cast:FloatingCast` | 4 | 4 | 20020413-1.c, 920618-1.c, ieee/pr67218.c, pr36343.c |
| `libc-call: __builtin_prefetch` | 4 | 4 | builtin-prefetch-1.c, builtin-prefetch-2.c, builtin-prefetch-4.c, builtin-prefetch-5.c |
| `unsupported:extern object 'b' has no definition in the translation unit` | 4 | 4 | alias-2.c, alias-3.c, alias-4.c, gcc/testsuite/gcc.dg/c23-bool-2.c |
| `unsupported:no layout for declared type 'const double'` | 4 | 4 | cbrt.c, ieee/hugeval.c, ieee/unsafe-fp-assoc-1.c, ieee/unsafe-fp-assoc.c |
| `unsupported:no layout for declared type 'union U'` | 4 | 4 | bitfld-6.c, bitfld-7.c, pr86492.c, pr88739.c |
| `libc-call: __builtin_abort` | 3 | 3 | gcc/testsuite/gcc.dg/c23-nullptr-5.c, pr77767.c, pr97325.c |
| `libc-call: __builtin_expect` | 3 | 3 | 00214.c, 20020418-1.c, pr115277.c |
| `unsupported:ExprWithCleanups` | 3 | 3 | 20041124-1.c, 950628-1.c, pr30185.c |
| `unsupported:function-to-pointer decay (inch 5)` | 3 | 3 | 20041212-1.c, 20101011-1.c, pr42231.c |
| `unsupported:no layout for declared type 'A'` | 3 | 3 | 20010118-1.c, restrict-1.c, strct-pack-2.c |
| `unsupported:no layout for declared type 'T'` | 3 | 3 | 920908-1.c, 931005-1.c, pr98474.c |
| `unsupported:no layout for declared type '_Complex float'` | 3 | 3 | complex-6.c, ieee/cdivchkf.c, pr38969.c |
| `unsupported:no layout for declared type 'enum bar'` | 3 | 3 | gcc/testsuite/gcc.dg/c23-tag-alias-1.c, gcc/testsuite/gcc.dg/c23-tag-alias-2.c, gcc/testsuite/gcc.dg/c23-tag-alias-3.c |
| `unsupported:no layout for declared type 'int[n % 1000 + 1]'` | 3 | 3 | 20040811-1.c, pr43220.c, vla-dealloc-1.c |
| `unsupported:no layout for declared type 'struct S[2]'` | 3 | 3 | 20050119-1.c, 20050119-2.c, pr71700.c |
| `unsupported:no layout for declared type 'struct foo'` | 3 | 3 | 00140.c, bf-pack-1.c, gcc/testsuite/gcc.dg/c23-tag-alias-7.c |
| `unsupported:no layout for declared type 'struct x'` | 3 | 3 | 20000113-1.c, 20020227-1.c, bitfld-1.c |
| `unsupported:type trait '__alignof'` | 3 | 3 | 20000223-1.c, align-3.c, zerolen-2.c |
| `unsupported:unbound declaration 'id15' (name 'x')` | 3 | 3 | 00119.c, 00123.c, 20090623-1.c |
| `unsupported:unbound declaration 'id180' (name 'stdout')` | 3 | 3 | 00189.c, fprintf-1.c, fprintf-chk-1.c |
| `unsupported:unbound declaration 'id25' (name 's')` | 3 | 3 | pr40404.c, pr48973-1.c, pr48973-2.c |
| `unsupported:unbound declaration 'id27' (name 'x')` | 3 | 3 | 20030209-1.c, 960405-1.c, 991030-1.c |
| `libc-call: calloc` | 2 | 2 | 00040.c, ipa-sra-2.c |
| `libc-call: memcmp` | 2 | 2 | 20050502-2.c, pr43236.c |
| `libc-call: open` | 2 | 2 | loop-2f.c, loop-2g.c |
| `libc-call: strchr` | 2 | 2 | 20000112-1.c, 20000910-2.c |
| `unsupported:extern object 'abs_called' has no definition in the translation unit` | 2 | 2 | builtins/abs-1-lib.c, builtins/uabs-1-lib.c |
| `unsupported:extern object 'x' has no definition in the translation unit` | 2 | 2 | 00094.c, 00110.c |
| `unsupported:floating literal lacks parser-native bits` | 2 | 2 | 920710-1.c, va-arg-26.c |
| `unsupported:goto skips a block declaration` | 2 | 2 | 00129.c, gcc/testsuite/gcc.dg/c23-labels-1.c |
| `unsupported:initializer list (inch 4)` | 2 | 2 | 00150.c, 00216.c |
| `unsupported:no layout for declared type 'Point'` | 2 | 2 | 20000808-1.c, 950607-2.c |
| `unsupported:no layout for declared type 'S'` | 2 | 2 | 00153.c, pr56799.c |
| `unsupported:no layout for declared type 'bitmap_iterator'` | 2 | 2 | 20090113-2.c, 20090113-3.c |
| `unsupported:no layout for declared type 'const float'` | 2 | 2 | ieee/20010114-2.c, ieee/20030331-1.c |
| `unsupported:no layout for declared type 'const struct try[6]'` | 2 | 2 | ieee/fp-cmp-4.c, ieee/fp-cmp-5.c |
| `unsupported:no layout for declared type 'double[4]'` | 2 | 2 | ieee/acc1.c, ieee/acc2.c |
| `unsupported:no layout for declared type 'enum E'` | 2 | 2 | 00054.c, 00055.c |
| `unsupported:no layout for declared type 'int *volatile'` | 2 | 2 | 20101025-1.c, builtin-prefetch-3.c |
| `unsupported:no layout for declared type 'jmp_buf'` | 2 | 2 | 20210505-1.c, pr56982.c |
| `unsupported:no layout for declared type 'long double'` | 2 | 2 | 20040208-1.c, ieee/pr29302-1.c |
| `unsupported:no layout for declared type 'st'` | 2 | 2 | pr31448-2.c, pr31448.c |
| `unsupported:no layout for declared type 'struct A'` | 2 | 2 | 20040709-1.c, 20040709-2.c |
| `unsupported:no layout for declared type 'struct S1'` | 2 | 2 | pr60017.c, stdarg-3.c |
| `unsupported:no layout for declared type 'struct U'` | 2 | 2 | pr22141-1.c, pr22141-2.c |
| `unsupported:no layout for declared type 'struct c'` | 2 | 2 | 990326-1.c, packed-aligned.c |
| `unsupported:no layout for declared type 'struct mouse_button_str'` | 2 | 2 | bitfld-8.c, bitfld-9.c |
| `unsupported:no layout for declared type 'struct packed_ushort'` | 2 | 2 | 20170401-1.c, pr45070.c |
| `unsupported:no layout for declared type 'struct1'` | 2 | 2 | pr86659-1.c, pr86659-2.c |
| `unsupported:no layout for declared type 'v16di'` | 2 | 2 | pr123625-2.c, pr126405-3.c |
| `unsupported:no layout for parameter type 'L'` | 2 | 2 | va-arg-12.c, va-arg-18.c |
| `unsupported:sizeof: no layout for operand type 'float'` | 2 | 2 | ieee/20000320-1.c, pr44468.c |
| `unsupported:sizeof: no layout for operand type 'struct A'` | 2 | 2 | bitfld-2.c, strlen-7.c |
| `unsupported:unbound declaration 'id15' (name 'a')` | 2 | 2 | gcc/testsuite/gcc.dg/c23-imaginary-constants-1.c, gcc/testsuite/gcc.dg/c23-imaginary-constants-7.c |
| `unsupported:unbound declaration 'id15' (name 'dnan')` | 2 | 2 | ieee/fp-cmp-6.c, ieee/fp-cmp-9.c |
| `unsupported:unbound declaration 'id19' (name 's')` | 2 | 2 | 00047.c, pr37882.c |
| `unsupported:unbound declaration 'id19' (name 'x')` | 2 | 2 | pr32244-1.c, pr34971.c |
| `unsupported:unbound declaration 'id21' (name 'a')` | 2 | 2 | 00091.c, pr56837.c |
| `unsupported:unbound declaration 'id21' (name 'pinf')` | 2 | 2 | ieee/compare-fp-1.c, ieee/compare-fp-4.c |
| `unsupported:unbound declaration 'id22' (name 's')` | 2 | 2 | pr67781.c, pr78436.c |
| `unsupported:unbound declaration 'id37' (name 'x')` | 2 | 2 | 931110-1.c, compndlit-1.c |
| `unsupported:unbound declaration 'id38' (name 'v')` | 2 | 2 | builtins/pr22237-1.c, builtins/pr22237.c |
| `unsupported:unbound declaration 'id39' (name 'X')` | 2 | 2 | 960215-1.c, regstack-1.c |
| `unsupported:unbound declaration 'id40' (name 'x')` | 2 | 2 | extzvsi.c, struct-ini-2.c |
| `unsupported:union initializer has no member` | 2 | 2 | pr15296.c, pr19687.c |
| `cast:FloatingComplexCast` | 1 | 1 | 20070614-1.c |
| `cast:FloatingRealToComplex` | 1 | 1 | complex-4.c |
| `cast:IntegralRealToComplex` | 1 | 1 | pr104604.c |
| `libc-call: __builtin_constant_p` | 1 | 1 | builtin-constant.c |
| `libc-call: __builtin_frame_address` | 1 | 1 | frame-address.c |
| `libc-call: __builtin_huge_val` | 1 | 1 | ieee/inf-3.c |
| `libc-call: __builtin_inf` | 1 | 1 | ieee/inf-2.c |
| `libc-call: __builtin_nanf` | 1 | 1 | ieee/pr119002.c |
| `libc-call: __builtin_snprintf` | 1 | 1 | pr78622.c |
| `libc-call: __builtin_strncpy` | 1 | 1 | pr93249.c |
| `libc-call: exit (an argument is not a literal 0 — which exit was reached is unknown)` | 1 | 1 | 970217-1.c |
| `libc-call: f` | 1 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: floor` | 1 | 1 | 990826-0.c |
| `libc-call: fopen` | 1 | 1 | 00187.c |
| `libc-call: main_test` | 1 | 1 | builtins/lib/main.c |
| `libc-call: mempcpy` | 1 | 1 | string-opt-18.c |
| `libc-call: sin` | 1 | 1 | ieee/mzero4.c |
| `libc-call: strncmp` | 1 | 1 | 20050218-1.c |
| `unsupported:AlignedAttr` | 1 | 1 | pr108064.c |
| `unsupported:GCCAsmStmt` | 1 | 1 | pr81588.c |
| `unsupported:GenericSelectionExpr` | 1 | 1 | gcc/testsuite/gcc.dg/c23-bool-1.c |
| `unsupported:TypeTraitExpr` | 1 | 1 | builtin-types-compatible-p.c |
| `unsupported:block-scope storage class 'extern' is outside the tier` | 1 | 1 | scope-1.c |
| `unsupported:call through an incompatible function-pointer cast` | 1 | 1 | call-trap-1.c |
| `unsupported:cannot initialize aggregate 'int'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-empty-init-1.c |
| `unsupported:compound literal initializer callback unavailable` | 1 | 1 | 20050929-1.c |
| `unsupported:extern object 'ReadyFlag_NotProperlyInitialized' has no definition in the translation unit` | 1 | 1 | pr31072.c |
| `unsupported:extern object 'aa' has no definition in the translation unit` | 1 | 1 | 20000403-1.c |
| `unsupported:extern object 'i' has no definition in the translation unit` | 1 | 1 | pure-1.c |
| `unsupported:extern object 'p' has no definition in the translation unit` | 1 | 1 | gcc/testsuite/gcc.dg/c23-unreachable-1.c |
| `unsupported:function instrumentation is outside the tier` | 1 | 1 | eeprof-1.c |
| `unsupported:long double integer-to-floating conversion` | 1 | 1 | 930622-2.c |
| `unsupported:no layout for compound literal type 'A'` | 1 | 1 | 20020206-2.c |
| `unsupported:no layout for compound literal type 'T'` | 1 | 1 | 20071029-1.c |
| `unsupported:no layout for compound literal type 'V'` | 1 | 1 | pr109040.c |
| `unsupported:no layout for declared type 'A0'` | 1 | 1 | va-arg-22.c |
| `unsupported:no layout for declared type 'DB_TXNLIST'` | 1 | 1 | 20011008-3.c |
| `unsupported:no layout for declared type 'Data[4]'` | 1 | 1 | 20010116-1.c |
| `unsupported:no layout for declared type 'PgHdr[5]'` | 1 | 1 | pr33870-1.c |
| `unsupported:no layout for declared type 'Q'` | 1 | 1 | simd-5.c |
| `unsupported:no layout for declared type 'RenderInfo'` | 1 | 1 | 20000605-1.c |
| `unsupported:no layout for declared type 'T0 *const'` | 1 | 1 | 991016-1.c |
| `unsupported:no layout for declared type 'TRIAL'` | 1 | 1 | strct-pack-1.c |
| `unsupported:no layout for declared type 'Test1'` | 1 | 1 | 990525-2.c |
| `unsupported:no layout for declared type 'U'` | 1 | 1 | 20180131-1.c |
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
| `unsupported:no layout for declared type 'const struct Df[8]'` | 1 | 1 | ieee/copysign1.c |
| `unsupported:no layout for declared type 'const struct a'` | 1 | 1 | pr100453.c |
| `unsupported:no layout for declared type 'const struct s'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-constexpr-2a.c |
| `unsupported:no layout for declared type 'const struct try[14]'` | 1 | 1 | ieee/fp-cmp-8.c |
| `unsupported:no layout for declared type 'creal_T[16]'` | 1 | 1 | pr93434.c |
| `unsupported:no layout for declared type 'double (*)()'` | 1 | 1 | 930608-1.c |
| `unsupported:no layout for declared type 'double (*)(float)'` | 1 | 1 | func-ptr-1.c |
| `unsupported:no layout for declared type 'double[1]'` | 1 | 1 | 20001017-1.c |
| `unsupported:no layout for declared type 'double[32]'` | 1 | 1 | pr59643.c |
| `unsupported:no layout for declared type 'double[6]'` | 1 | 1 | 930614-1.c |
| `unsupported:no layout for declared type 'double[n]'` | 1 | 1 | 920929-1.c |
| `unsupported:no layout for declared type 'enum e'` | 1 | 1 | enum-3.c |
| `unsupported:no layout for declared type 'enum fred'` | 1 | 1 | 00170.c |
| `unsupported:no layout for declared type 'float[16]'` | 1 | 1 | loop-ivopts-1.c |
| `unsupported:no layout for declared type 'float[32]'` | 1 | 1 | ieee/pr72824.c |
| `unsupported:no layout for declared type 'float[3]'` | 1 | 1 | 20021118-2.c |
| `unsupported:no layout for declared type 'float[8]'` | 1 | 1 | ieee/copysign2.c |
| `unsupported:no layout for declared type 'float[8][2][8][2]'` | 1 | 1 | 930614-2.c |
| `unsupported:no layout for declared type 'four_quarters'` | 1 | 1 | 921123-2.c |
| `unsupported:no layout for declared type 'gfc_array_i4'` | 1 | 1 | 20090113-1.c |
| `unsupported:no layout for declared type 'i386_operand_type'` | 1 | 1 | pr40493.c |
| `unsupported:no layout for declared type 'info_t'` | 1 | 1 | 20100430-1.c |
| `unsupported:no layout for declared type 'int (*(*)(int, int))(int, int)'` | 1 | 1 | 00124.c |
| `unsupported:no layout for declared type 'int (*)(int, int)'` | 1 | 1 | 991112-1.c |
| `unsupported:no layout for declared type 'int (*)[++i]'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-auto-2.c |
| `unsupported:no layout for declared type 'int ***volatile'` | 1 | 1 | pr58277-2.c |
| `unsupported:no layout for declared type 'int32_t'` | 1 | 1 | 00104.c |
| `unsupported:no layout for declared type 'int[len][len]'` | 1 | 1 | 20221006-1.c |
| `unsupported:no layout for declared type 'io'` | 1 | 1 | 20031201-1.c |
| `unsupported:no layout for declared type 'material_type'` | 1 | 1 | 991019-1.c |
| `unsupported:no layout for declared type 'mp_int'` | 1 | 1 | 20180226-1.c |
| `unsupported:no layout for declared type 'neon_s8'` | 1 | 1 | pr42833.c |
| `unsupported:no layout for declared type 'object'` | 1 | 1 | 980223.c |
| `unsupported:no layout for declared type 's'` | 1 | 1 | 00046.c |
| `unsupported:no layout for declared type 'spinlock_t'` | 1 | 1 | zero-struct-2.c |
| `unsupported:no layout for declared type 'struc'` | 1 | 1 | 20001101.c |
| `unsupported:no layout for declared type 'struct B'` | 1 | 1 | pr15262-2.c |
| `unsupported:no layout for declared type 'struct D'` | 1 | 1 | 20050613-1.c |
| `unsupported:no layout for declared type 'struct E'` | 1 | 1 | pr39339.c |
| `unsupported:no layout for declared type 'struct S0'` | 1 | 1 | pr78170.c |
| `unsupported:no layout for declared type 'struct S[21]'` | 1 | 1 | pr70602.c |
| `unsupported:no layout for declared type 'struct S[6]'` | 1 | 1 | pr58570.c |
| `unsupported:no layout for declared type 'struct a'` | 1 | 1 | 20031211-1.c |
| `unsupported:no layout for declared type 'struct bar'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-tag-alias-4.c |
| `unsupported:no layout for declared type 'struct brfic_args'` | 1 | 1 | 20001026-1.c |
| `unsupported:no layout for declared type 'struct complex'` | 1 | 1 | complex-3.c |
| `unsupported:no layout for declared type 'struct event'` | 1 | 1 | 20111212-1.c |
| `unsupported:no layout for declared type 'struct f'` | 1 | 1 | bitfld-10.c |
| `unsupported:no layout for declared type 'struct g'` | 1 | 1 | zero-struct-1.c |
| `unsupported:no layout for declared type 'struct mystruct'` | 1 | 1 | pr70566.c |
| `unsupported:no layout for declared type 'struct printf_spec'` | 1 | 1 | 20190820-1.c |
| `unsupported:no layout for declared type 'struct product_iSfd_'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-tag-5.c |
| `unsupported:no layout for declared type 'struct reg_stat'` | 1 | 1 | pr30778.c |
| `unsupported:no layout for declared type 'struct test2'` | 1 | 1 | pr29156.c |
| `unsupported:no layout for declared type 'struct tmp'` | 1 | 1 | bf64-1.c |
| `unsupported:no layout for declared type 'struct tree_type'` | 1 | 1 | pr31169.c |
| `unsupported:no layout for declared type 'struct tty_driver'` | 1 | 1 | struct-cpy-1.c |
| `unsupported:no layout for declared type 'struct write_data'` | 1 | 1 | 20000815-1.c |
| `unsupported:no layout for declared type 'struct_list'` | 1 | 1 | 921113-1.c |
| `unsupported:no layout for declared type 't'` | 1 | 1 | 920810-1.c |
| `unsupported:no layout for declared type 't1'` | 1 | 1 | divconst-1.c |
| `unsupported:no layout for declared type 't_be'` | 1 | 1 | 960416-1.c |
| `unsupported:no layout for declared type 'three_byte_t'` | 1 | 1 | struct-ret-2.c |
| `unsupported:no layout for declared type 'three_char_t'` | 1 | 1 | strct-pack-4.c |
| `unsupported:no layout for declared type 'token'` | 1 | 1 | enum-1.c |
| `unsupported:no layout for declared type 'uint32_t'` | 1 | 1 | 20120111-1.c |
| `unsupported:no layout for declared type 'uint32_t[16]'` | 1 | 1 | pr65369.c |
| `unsupported:no layout for declared type 'union U1'` | 1 | 1 | 20181120-1.c |
| `unsupported:no layout for declared type 'union Y'` | 1 | 1 | pr92904.c |
| `unsupported:no layout for declared type 'union _D_rep'` | 1 | 1 | pr42691.c |
| `unsupported:no layout for declared type 'union at6'` | 1 | 1 | pr23324.c |
| `unsupported:no layout for declared type 'union bf_or_uint32'` | 1 | 1 | bswap-2.c |
| `unsupported:no layout for declared type 'union tree_node'` | 1 | 1 | 00218.c |
| `unsupported:no layout for declared type 'union u'` | 1 | 1 | 20000603-1.c |
| `unsupported:no layout for declared type 'unit_flags'` | 1 | 1 | 20090527-1.c |
| `unsupported:no layout for declared type 'v4qi'` | 1 | 1 | pr60960.c |
| `unsupported:no layout for declared type 'v8qi'` | 1 | 1 | simd-6.c |
| `unsupported:no layout for declared type 'void *volatile'` | 1 | 1 | pr84521.c |
| `unsupported:no layout for declared type 'volatile a_struct'` | 1 | 1 | 20010518-2.c |
| `unsupported:no layout for declared type 'volatile double'` | 1 | 1 | 980709-1.c |
| `unsupported:no layout for declared type 'volatile enum X'` | 1 | 1 | 20030903-1.c |
| `unsupported:no layout for declared type 'volatile long double'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-float-12.c |
| `unsupported:no layout for declared type 'wchar_t[21]'` | 1 | 1 | 00220.c |
| `unsupported:no layout for field 'n'` | 1 | 1 | pr39100.c |
| `unsupported:no layout for field 'y'` | 1 | 1 | 00053.c |
| `unsupported:no layout for parameter type 'TYPE'` | 1 | 1 | va-arg-16.c |
| `unsupported:no layout for parameter type 'const struct b *restrict'` | 1 | 1 | 20001024-1.c |
| `unsupported:no layout for parameter type 'const unsigned int *const'` | 1 | 1 | pr63209.c |
| `unsupported:no layout for parameter type 'foo_t *const'` | 1 | 1 | pr33669.c |
| `unsupported:no layout for parameter type 'int **restrict'` | 1 | 1 | 20080506-2.c |
| `unsupported:no layout for parameter type 'int *restrict'` | 1 | 1 | pr38212.c |
| `unsupported:non-object declaration in a block` | 1 | 1 | 00078.c |
| `unsupported:not an integer type: 'T'` | 1 | 1 | pr84169.c |
| `unsupported:not an lvalue: PredefinedExpr` | 1 | 1 | 20001011-1.c |
| `unsupported:operator '-' on pointers from different arrays` | 1 | 1 | 950710-1.c |
| `unsupported:operator '-' on pointers without array provenance` | 1 | 1 | 980701-1.c |
| `unsupported:printf` | 1 | 1 | 00215.c |
| `unsupported:sizeof: no layout for operand type 'PT[9]'` | 1 | 1 | 00205.c |
| `unsupported:sizeof: no layout for operand type 'Union'` | 1 | 1 | 20051113-1.c |
| `unsupported:sizeof: no layout for operand type '_Atomic(unsigned char)'` | 1 | 1 | gcc/testsuite/gcc.dg/atomic/c23-stdatomic-lockfree-char8_t.c |
| `unsupported:sizeof: no layout for operand type 'c'` | 1 | 1 | 20040411-1.c |
| `unsupported:sizeof: no layout for operand type 'double'` | 1 | 1 | 991228-1.c |
| `unsupported:sizeof: no layout for operand type 'foo_t'` | 1 | 1 | 941014-2.c |
| `unsupported:sizeof: no layout for operand type 'int (*volatile[6])(void)'` | 1 | 1 | bcp-1.c |
| `unsupported:sizeof: no layout for operand type 'struct S'` | 1 | 1 | 20120105-1.c |
| `unsupported:sizeof: no layout for operand type 'struct VEC_char_base'` | 1 | 1 | pr41395-2.c |
| `unsupported:sizeof: no layout for operand type 'struct bitfield'` | 1 | 1 | pr111613.c |
| `unsupported:sizeof: no layout for operand type 'struct tree_common'` | 1 | 1 | 20000914-1.c |
| `unsupported:sprintf` | 1 | 1 | pr79327.c |
| `unsupported:src/20000412-5.c` | 1 | 1 | 20000412-5.c |
| `unsupported:src/20020225-2.c` | 1 | 1 | 20020225-2.c |
| `unsupported:src/20040307-1.c` | 1 | 1 | 20040307-1.c |
| `unsupported:src/20040331-1.c` | 1 | 1 | 20040331-1.c |
| `unsupported:src/20050316-3.c` | 1 | 1 | 20050316-3.c |
| `unsupported:src/921016-1.c` | 1 | 1 | 921016-1.c |
| `unsupported:src/930628-1.c` | 1 | 1 | 930628-1.c |
| `unsupported:src/bf-layout-1.c` | 1 | 1 | bf-layout-1.c |
| `unsupported:src/bf-sign-1.c` | 1 | 1 | bf-sign-1.c |
| `unsupported:src/ffs-2.c` | 1 | 1 | ffs-2.c |
| `unsupported:src/ieee/930529-1.c` | 1 | 1 | ieee/930529-1.c |
| `unsupported:src/ieee/minuszero.c` | 1 | 1 | ieee/minuszero.c |
| `unsupported:src/ieee/mul-subnormal-single-1.c` | 1 | 1 | ieee/mul-subnormal-single-1.c |
| `unsupported:src/ieee/pr30704.c` | 1 | 1 | ieee/pr30704.c |
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
| `unsupported:src/strncmp-1.c` | 1 | 1 | strncmp-1.c |
| `unsupported:strcmp` | 1 | 1 | p18298.c |
| `unsupported:strlen` | 1 | 1 | strlen-3.c |
| `unsupported:unbound declaration 'id103' (name 'test')` | 1 | 1 | pr71083.c |
| `unsupported:unbound declaration 'id126' (name 'f')` | 1 | 1 | gcc/testsuite/gcc.dg/c23-float-5.c |
| `unsupported:unbound declaration 'id137' (name 'tmp')` | 1 | 1 | pr36034-2.c |
| `unsupported:unbound declaration 'id142' (name 'tmp')` | 1 | 1 | pr36034-1.c |
| `unsupported:unbound declaration 'id15' (name 'array0')` | 1 | 1 | postmod-1.c |
| `unsupported:unbound declaration 'id15' (name 'extfunc')` | 1 | 1 | pr67037.c |
| `unsupported:unbound declaration 'id15' (name 'f1')` | 1 | 1 | complex-7.c |
| `unsupported:unbound declaration 'id15' (name 'fptr')` | 1 | 1 | 00088.c |
| `unsupported:unbound declaration 'id15' (name 'vd')` | 1 | 1 | 20120919-1.c |
| `unsupported:unbound declaration 'id151' (name 's')` | 1 | 1 | pr91597.c |
| `unsupported:unbound declaration 'id16139' (name 'cu')` | 1 | 1 | strlen-5.c |
| `unsupported:unbound declaration 'id18' (name 'a')` | 1 | 1 | pr65427.c |
| `unsupported:unbound declaration 'id18' (name 'g')` | 1 | 1 | 20031214-1.c |
| `unsupported:unbound declaration 'id18' (name 's')` | 1 | 1 | 20051104-1.c |
| `unsupported:unbound declaration 'id18' (name 'x')` | 1 | 1 | pr33382.c |
| `unsupported:unbound declaration 'id185' (name 'w')` | 1 | 1 | pr47337.c |
| `unsupported:unbound declaration 'id19' (name 'b')` | 1 | 1 | bitfld-signed1-1.c |
| `unsupported:unbound declaration 'id19' (name 'f')` | 1 | 1 | signed1bitfield-1.c |
| `unsupported:unbound declaration 'id197' (name 't')` | 1 | 1 | 20011113-1.c |
| `unsupported:unbound declaration 'id20' (name 'b')` | 1 | 1 | pr59388.c |
| `unsupported:unbound declaration 'id21' (name 'b')` | 1 | 1 | pr82192.c |
| `unsupported:unbound declaration 'id21' (name 'g1s')` | 1 | 1 | pr42248.c |
| `unsupported:unbound declaration 'id21' (name 's')` | 1 | 1 | 20041201-1.c |
| `unsupported:unbound declaration 'id21' (name 'v')` | 1 | 1 | 00024.c |
| `unsupported:unbound declaration 'id22' (name 'b')` | 1 | 1 | pr58726.c |
| `unsupported:unbound declaration 'id22' (name 'c')` | 1 | 1 | pr103417.c |
| `unsupported:unbound declaration 'id22' (name 't')` | 1 | 1 | packed-2.c |
| `unsupported:unbound declaration 'id23' (name 'a')` | 1 | 1 | pr44164.c |
| `unsupported:unbound declaration 'id23' (name 'f')` | 1 | 1 | 20100316-1.c |
| `unsupported:unbound declaration 'id23' (name 'u')` | 1 | 1 | pr97073.c |
| `unsupported:unbound declaration 'id24' (name 'a1')` | 1 | 1 | 20010924-1.c |
| `unsupported:unbound declaration 'id25' (name 'c')` | 1 | 1 | pr52209.c |
| `unsupported:unbound declaration 'id25' (name 'f')` | 1 | 1 | pr19689.c |
| `unsupported:unbound declaration 'id25' (name 't')` | 1 | 1 | vrp-7.c |
| `unsupported:unbound declaration 'id25' (name 'v')` | 1 | 1 | 20050215-1.c |
| `unsupported:unbound declaration 'id25' (name 'x')` | 1 | 1 | 20030109-1.c |
| `unsupported:unbound declaration 'id26' (name 'a')` | 1 | 1 | 20020213-1.c |
| `unsupported:unbound declaration 'id26' (name 'u')` | 1 | 1 | pr87053.c |
| `unsupported:unbound declaration 'id26' (name 'v')` | 1 | 1 | pr43784.c |
| `unsupported:unbound declaration 'id27' (name 'a')` | 1 | 1 | 20031215-1.c |
| `unsupported:unbound declaration 'id27' (name 'd')` | 1 | 1 | 20001121-1.c |
| `unsupported:unbound declaration 'id27' (name 'f')` | 1 | 1 | 921208-1.c |
| `unsupported:unbound declaration 'id27' (name 'gd')` | 1 | 1 | 20021120-1.c |
| `unsupported:unbound declaration 'id27' (name 's2848')` | 1 | 1 | pr38151.c |
| `unsupported:unbound declaration 'id28' (name 'arr')` | 1 | 1 | pr55750.c |
| `unsupported:unbound declaration 'id28' (name 's')` | 1 | 1 | pr31136.c |
| `unsupported:unbound declaration 'id28' (name 'sv')` | 1 | 1 | 20071211-1.c |
| `unsupported:unbound declaration 'id28' (name 'terminate_me')` | 1 | 1 | pr54937.c |
| `unsupported:unbound declaration 'id28' (name 'v')` | 1 | 1 | 00050.c |
| `unsupported:unbound declaration 'id28' (name 'x')` | 1 | 1 | bitfld-4.c |
| `unsupported:unbound declaration 'id29' (name 'a')` | 1 | 1 | pr44575.c |
| `unsupported:unbound declaration 'id29' (name 'f1')` | 1 | 1 | floatunsisf-1.c |
| `unsupported:unbound declaration 'id29' (name 't')` | 1 | 1 | 20051012-1.c |
| `unsupported:unbound declaration 'id30' (name 'b')` | 1 | 1 | 20131127-1.c |
| `unsupported:unbound declaration 'id30' (name 'f')` | 1 | 1 | pr98366.c |
| `unsupported:unbound declaration 'id30' (name 'u')` | 1 | 1 | 20050604-1.c |
| `unsupported:unbound declaration 'id30' (name 'x')` | 1 | 1 | 20011019-1.c |
| `unsupported:unbound declaration 'id30' (name 'y')` | 1 | 1 | ieee/pr28634.c |
| `unsupported:unbound declaration 'id31' (name 't')` | 1 | 1 | 980602-2.c |
| `unsupported:unbound declaration 'id31' (name 'wordlist')` | 1 | 1 | 20000412-1.c |
| `unsupported:unbound declaration 'id32' (name 'foo')` | 1 | 1 | anon-1.c |
| `unsupported:unbound declaration 'id32' (name 'node')` | 1 | 1 | 20030224-2.c |
| `unsupported:unbound declaration 'id32' (name 's')` | 1 | 1 | pr38422.c |
| `unsupported:unbound declaration 'id33' (name 'entry')` | 1 | 1 | zerolen-1.c |
| `unsupported:unbound declaration 'id33' (name 'n1')` | 1 | 1 | ieee/builtin-nan-1.c |
| `unsupported:unbound declaration 'id33' (name 't')` | 1 | 1 | packed-1.c |
| `unsupported:unbound declaration 'id33' (name 'x')` | 1 | 1 | 921112-1.c |
| `unsupported:unbound declaration 'id339' (name 'g_this')` | 1 | 1 | 20030714-1.c |
| `unsupported:unbound declaration 'id34' (name 'foo')` | 1 | 1 | 960301-1.c |
| `unsupported:unbound declaration 'id34' (name 'zerod')` | 1 | 1 | ieee/mzero3.c |
| `unsupported:unbound declaration 'id36' (name 'actual_function')` | 1 | 1 | 00210.c |
| `unsupported:unbound declaration 'id36' (name 's')` | 1 | 1 | 930408-1.c |
| `unsupported:unbound declaration 'id37' (name 'a')` | 1 | 1 | bitfld-3.c |
| `unsupported:unbound declaration 'id37' (name 'b')` | 1 | 1 | 20040629-1.c |
| `unsupported:unbound declaration 'id37' (name 'pts')` | 1 | 1 | 920625-1.c |
| `unsupported:unbound declaration 'id38' (name 's')` | 1 | 1 | 20000801-3.c |
| `unsupported:unbound declaration 'id42' (name 'x')` | 1 | 1 | ieee/20041213-1.c |
| `unsupported:unbound declaration 'id42' (name 'y')` | 1 | 1 | 20010904-1.c |
| `unsupported:unbound declaration 'id420' (name 'buffer')` | 1 | 1 | 20060420-1.c |
| `unsupported:unbound declaration 'id426' (name 'array')` | 1 | 1 | pr34456.c |
| `unsupported:unbound declaration 'id43' (name 'buf')` | 1 | 1 | pr93908.c |
| `unsupported:unbound declaration 'id43' (name 'y')` | 1 | 1 | 20010904-2.c |
| `unsupported:unbound declaration 'id45' (name 'k')` | 1 | 1 | simd-1.c |
| `unsupported:unbound declaration 'id45' (name 's')` | 1 | 1 | 20081117-1.c |
| `unsupported:unbound declaration 'id48' (name 'curval')` | 1 | 1 | 960117-1.c |
| `unsupported:unbound declaration 'id487' (name 'MyPte')` | 1 | 1 | 20020402-2.c |
| `unsupported:unbound declaration 'id49' (name 'result')` | 1 | 1 | struct-ini-3.c |
| `unsupported:unbound declaration 'id49' (name 's_c_f')` | 1 | 1 | align-2.c |
| `unsupported:unbound declaration 'id50' (name 'ws')` | 1 | 1 | widechar-2.c |
| `unsupported:unbound declaration 'id515' (name 'point_array')` | 1 | 1 | 00195.c |
| `unsupported:unbound declaration 'id52' (name 'x')` | 1 | 1 | bf-sign-2.c |
| `unsupported:unbound declaration 'id561' (name 'b')` | 1 | 1 | pr103209.c |
| `unsupported:unbound declaration 'id66' (name 'k')` | 1 | 1 | simd-2.c |
| `unsupported:unbound declaration 'id67' (name 'z')` | 1 | 1 | complex-5.c |
| `unsupported:unbound declaration 'id725' (name 'input')` | 1 | 1 | pr28982a.c |
| `unsupported:unbound declaration 'id74' (name 'p')` | 1 | 1 | pr64242.c |
| `unsupported:unbound declaration 'id751' (name 'input')` | 1 | 1 | pr28982b.c |
| `unsupported:unbound declaration 'id84' (name 'a')` | 1 | 1 | 20041113-1.c |
| `unsupported:unbound declaration 'id95' (name 'tmp')` | 1 | 1 | 991118-1.c |
| `unsupported:unknown enum declaration 'id17' (name 'X')` | 1 | 1 | 00120.c |
| `unsupported:unknown enum declaration 'id29' (name 'BAR')` | 1 | 1 | enum-2.c |
| `unsupported:unknown enum declaration 'id41' (name 'N')` | 1 | 1 | 20011219-1.c |
| `unsupported:unknown enum declaration 'id513' (name 'a')` | 1 | 1 | 00198.c |
| `unsupported:unnamed pointer parameter (array-bound effects are not retained by clang)` | 1 | 1 | gcc/testsuite/gcc.dg/c23-parm-omit-3.c |
