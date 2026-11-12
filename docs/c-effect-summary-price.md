# C unsequenced-effect summary price

Parser-envelope census only; no purity theorem is claimed.

| file | functions | transitive pure shapes | calls / variable refs |
| --- | ---: | ---: | --- |
| `00121.c` | 3 | 3 | `f,g` / `none` |
| `20001228-1.c` | 3 | 0 | `abort,exit,foo1,foo2` / `u` |
| `20050218-1.c` | 2 | 0 | `abort,foo,strlen,strncmp` / `a,i,j` |
| `20051021-1.c` | 3 | 0 | `abort,foo1,foo2` / `count` |
| `20060102-1.c` | 2 | 1 | `abort,f` / `one` |
| `20060929-1.c` | 4 | 0 | `abort,bar,baz,foo` / `i,j,p` |
| `20230510-1.c` | 3 | 1 | `__builtin_abort,f,f1` / `a,i,j,t` |
| `20230802-1.c` | 7 | 0 | `__builtin_abort,bar,bar_v,baz,baz_v,foo,foo_v` / `t,y` |
| `920501-6.c` | 0 | 0 | `none` / `none` |
| `930930-2.c` | 3 | 0 | `abort,exit,test_endianness,test_endianness_vol` / `dw` |
| `991202-3.c` | 4 | 4 | `abort,exit,f,g,h` / `none` |
| `bitops-1.c` | 7 | 6 | `__builtin_abort,h0,h1,i0,i1,k0,k1` / `A,B,a,b,numvalues,values` |
| `bswap-1.c` | 3 | 1 | `__builtin_abort,__builtin_bswap64,f,g` / `a,b,i` |
| `bswap-3.c` | 3 | 2 | `__builtin_abort,__builtin_bswap32,f,g` / `b` |
| `builtin-bitops-1.c` | 13 | 0 | `__builtin_clrsb,__builtin_clrsbl,__builtin_clrsbll,__builtin_clz,__builtin_clzl,__builtin_clzll,__builtin_ctz,__builtin_ctzl,__builtin_ctzll,__builtin_ffs,__builtin_ffsl,__builtin_ffsll,__builtin_parity,__builtin_parityl,__builtin_parityll,__builtin_popcount,__builtin_popcountl,__builtin_popcountll,abort,exit,my_clrsb,my_clrsbl,my_clrsbll,my_clz,my_clzl,my_clzll,my_ctz,my_ctzl,my_ctzll,my_ffs,my_ffsl,my_ffsll,my_parity,my_parityl,my_parityll,my_popcount,my_popcountl,my_popcountll` / `count,i,ints,leading,longlongs,longs` |
| `cvt-1.c` | 4 | 4 | `abort,exit,f,g1,g2` / `none` |
| `divconst-2.c` | 4 | 3 | `abort,exit,f,r,std_eqn` / `i,nums` |
| `ieee/pr109386.c` | 2 | 0 | `__builtin_abort,__builtin_fabsf,__builtin_inff,__builtin_isinf,__builtin_nanf,foo` / `u,v` |
| `minmaxcmp-1.c` | 25 | 0 | `__builtin_abort,max_eq_,max_eq_volatile,max_ge_,max_ge_volatile,max_gt_,max_gt_volatile,max_le_,max_le_volatile,max_lt_,max_lt_volatile,max_ne_,max_ne_volatile,min_eq_,min_eq_volatile,min_ge_,min_ge_volatile,min_gt_,min_gt_volatile,min_le_,min_le_volatile,min_lt_,min_lt_volatile,min_ne_,min_ne_volatile` / `x,y` |
| `pr107881-1.c` | 145 | 0 | `__builtin_abort,ge_eq_eq_,ge_eq_eq_volatile,ge_eq_ne_,ge_eq_ne_volatile,ge_eq_xor_,ge_eq_xor_volatile,ge_ge_eq_,ge_ge_eq_volatile,ge_ge_ne_,ge_ge_ne_volatile,ge_ge_xor_,ge_ge_xor_volatile,ge_gt_eq_,ge_gt_eq_volatile,ge_gt_ne_,ge_gt_ne_volatile,ge_gt_xor_,ge_gt_xor_volatile,ge_le_eq_,ge_le_eq_volatile,ge_le_ne_,ge_le_ne_volatile,ge_le_xor_,ge_le_xor_volatile,ge_lt_eq_,ge_lt_eq_volatile,ge_lt_ne_,ge_lt_ne_volatile,ge_lt_xor_,ge_lt_xor_volatile,ge_ne_eq_,ge_ne_eq_volatile,ge_ne_ne_,ge_ne_ne_volatile,ge_ne_xor_,ge_ne_xor_volatile,gt_eq_eq_,gt_eq_eq_volatile,gt_eq_ne_,gt_eq_ne_volatile,gt_eq_xor_,gt_eq_xor_volatile,gt_ge_eq_,gt_ge_eq_volatile,gt_ge_ne_,gt_ge_ne_volatile,gt_ge_xor_,gt_ge_xor_volatile,gt_gt_eq_,gt_gt_eq_volatile,gt_gt_ne_,gt_gt_ne_volatile,gt_gt_xor_,gt_gt_xor_volatile,gt_le_eq_,gt_le_eq_volatile,gt_le_ne_,gt_le_ne_volatile,gt_le_xor_,gt_le_xor_volatile,gt_lt_eq_,gt_lt_eq_volatile,gt_lt_ne_,gt_lt_ne_volatile,gt_lt_xor_,gt_lt_xor_volatile,gt_ne_eq_,gt_ne_eq_volatile,gt_ne_ne_,gt_ne_ne_volatile,gt_ne_xor_,gt_ne_xor_volatile,le_eq_eq_,le_eq_eq_volatile,le_eq_ne_,le_eq_ne_volatile,le_eq_xor_,le_eq_xor_volatile,le_ge_eq_,le_ge_eq_volatile,le_ge_ne_,le_ge_ne_volatile,le_ge_xor_,le_ge_xor_volatile,le_gt_eq_,le_gt_eq_volatile,le_gt_ne_,le_gt_ne_volatile,le_gt_xor_,le_gt_xor_volatile,le_le_eq_,le_le_eq_volatile,le_le_ne_,le_le_ne_volatile,le_le_xor_,le_le_xor_volatile,le_lt_eq_,le_lt_eq_volatile,le_lt_ne_,le_lt_ne_volatile,le_lt_xor_,le_lt_xor_volatile,le_ne_eq_,le_ne_eq_volatile,le_ne_ne_,le_ne_ne_volatile,le_ne_xor_,le_ne_xor_volatile,lt_eq_eq_,lt_eq_eq_volatile,lt_eq_ne_,lt_eq_ne_volatile,lt_eq_xor_,lt_eq_xor_volatile,lt_ge_eq_,lt_ge_eq_volatile,lt_ge_ne_,lt_ge_ne_volatile,lt_ge_xor_,lt_ge_xor_volatile,lt_gt_eq_,lt_gt_eq_volatile,lt_gt_ne_,lt_gt_ne_volatile,lt_gt_xor_,lt_gt_xor_volatile,lt_le_eq_,lt_le_eq_volatile,lt_le_ne_,lt_le_ne_volatile,lt_le_xor_,lt_le_xor_volatile,lt_lt_eq_,lt_lt_eq_volatile,lt_lt_ne_,lt_lt_ne_volatile,lt_lt_xor_,lt_lt_xor_volatile,lt_ne_eq_,lt_ne_eq_volatile,lt_ne_ne_,lt_ne_ne_volatile,lt_ne_xor_,lt_ne_xor_volatile` / `x,y` |
| `pr110666-1.c` | 25 | 24 | `__builtin_abort,eqeq_0,eqeq_0_v,eqeq_1,eqeq_1_v,eqeq_2,eqeq_2_v,eqne_0,eqne_0_v,eqne_1,eqne_1_v,eqne_2,eqne_2_v,neeq_0,neeq_0_v,neeq_1,neeq_1_v,neeq_2,neeq_2_v,nene_0,nene_0_v,nene_1,nene_1_v,nene_2,nene_2_v` / `n` |
| `pr111431-1.c` | 8 | 0 | `__builtin_abort,func_0_,func_0_volatile,func_1_,func_1_volatile,func_5_,func_5_volatile` / `a,b` |
| `pr17377.c` | 3 | 0 | `__builtin_return_address,abort,exit,f,y` / `calls,v,x` |
| `pr20100-1.c` | 8 | 0 | `abort,curr_g,curr_p,exit,frob,get_n,inc_g,next_g,ring_empty` / `e,g,n,org_g,p` |
| `pr20621-1.c` | 2 | 1 | `foo` / `gb` |
| `pr33142.c` | 2 | 1 | `abort,abs,lisp_atan2` / `dx,dy` |
| `pr42721.c` | 2 | 1 | `abort,foo` / `a,b,c` |
| `pr44858.c` | 3 | 1 | `abort,bar,foo` / `a,b,c` |
| `pr55137.c` | 4 | 4 | `abort,bar,baz,foo` / `none` |
| `pr57875.c` | 1 | 0 | `abort` / `a,b,c,d,e,f,i` |
| `pr58943.c` | 2 | 0 | `__builtin_abort,foo` / `x` |
| `pr65215-2.c` | 3 | 2 | `__builtin_abort,bar,foo` / `l` |
| `pr68648.c` | 3 | 1 | `__builtin_abort,bar,foo` / `c` |
| `pr82524.c` | 3 | 1 | `__builtin_abort,bar,foo` / `a,b,c,v,w,z` |
| `pr91635.c` | 5 | 0 | `__builtin_abort,__builtin_add_overflow,bar,baz,foo,qux` / `b,c,u,v,w,x` |
| `pr93213.c` | 3 | 0 | `__builtin_abort,__builtin_memcpy,__builtin_memmove,__builtin_mul_overflow,bar,foo` / `a,b,c,p,u128_0,x` |
| `subcmp-1.c` | 33 | 0 | `__builtin_abort,ge_le_ge_,ge_le_ge_volatile,ge_le_gt_,ge_le_gt_volatile,ge_le_le_,ge_le_le_volatile,ge_le_lt_,ge_le_lt_volatile,gt_lt_ge_,gt_lt_ge_volatile,gt_lt_gt_,gt_lt_gt_volatile,gt_lt_le_,gt_lt_le_volatile,gt_lt_lt_,gt_lt_lt_volatile,le_ge_ge_,le_ge_ge_volatile,le_ge_gt_,le_ge_gt_volatile,le_ge_le_,le_ge_le_volatile,le_ge_lt_,le_ge_lt_volatile,lt_gt_ge_,lt_gt_ge_volatile,lt_gt_gt_,lt_gt_gt_volatile,lt_gt_le_,lt_gt_le_volatile,lt_gt_lt_,lt_gt_lt_volatile` / `x,y` |
