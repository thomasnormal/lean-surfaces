# Subroutines — repricing boundary

The current public SystemVerilog envelope does not admit user `function`,
`task`, or DPI subroutine declarations as ordinary module members. Such a
declaration is retained as `SubroutineSymbol:Subroutine`. The existing
system-task and intrinsic query paths are separate contracts and do not make
arbitrary user calls live.

## Why declarations remain a boundary

A function call needs a callable activation: formal argument conversions,
return-value context, local lifetime, recursion and any state or output effect
must be represented in the executable surface. A task additionally may block,
schedule work, or update output/ref/inout arguments across a retained
continuation. Dropping a declaration because one call is constant-folded would
be unsound for another call site or for a function with side effects.

Constant functions are not a generic escape hatch. They have a separate
elaboration-time legality and evaluation rule, including restrictions on
timing, calls, storage and recursion; the resulting constant can be used in a
parameter or type without providing a runtime callable frame. DPI imports add
an external implementation, ABI and oracle boundary even when their source
signature looks like an ordinary function or task.

The admitted surface therefore stays explicit:

* fixed metadata queries, `$clog2`, dynamic integral `$cast`, `$display`,
  `$write`, `$finish` and `$stop` use their existing intrinsic contracts;
* user functions, user tasks, and methods remain `SubroutineSymbol:Subroutine`
  until callable frames and argument/return storage are represented; and
* DPI imports, exported routines, timing tasks and other external calls remain
  loud rather than being treated as pure arithmetic or no-ops.

## 2026-10-21 census and decision

The fresh 22,043-path census records `SubroutineSymbol:Subroutine` in **1,714**
files: **108** are subroutine-only and **1,606** co-occur with another wall.
The read-only repricer finds **126** unsupported declaration instances in the
108 sole files:

| declaration shape | instances | files |
|---|---:|---:|
| function declaration | 70 | 63 |
| task declaration | 23 | 20 |
| DPI import | 33 | 28 |

The file column overlaps when a source has several declaration shapes. The
function rows include pure/constant candidates, side-effecting bodies and
timing/fork-invalid examples; tasks include both ordinary and timing forms.
The DPI rows cover C linkage, context/pure qualifiers, invalid signatures and
version strings. No single source shape supplies the missing callable or
external-effect representation, so no subfamily is admitted by this item.

Reproduce the table with:

```text
python3.9 extractors/sv/subroutine_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reads each source in process and writes no envelope beside the
corpus. Its declaration-shape counts are telemetry, not a callable runtime.
