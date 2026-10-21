# Primitive instances — repricing boundary

The legacy envelope does not admit gate, switch, or pull primitive instances
as ordinary expressions. A concrete primitive is retained as
`PrimitiveInstanceSymbol:PrimitiveInstance`. The existing scalar and packed
evaluators describe values and procedural stores; they do not describe a
continuous primitive driver.

## Why primitives remain a boundary

Gate and switch primitives continuously drive nets. Their outputs observe
four-state inputs, drive strengths and optional inertial delays; `bufif` and
`notif` additionally turn a driver off. MOS and tran families propagate or
reduce strength through bidirectional paths. Pullup and pulldown provide
implicit drivers even when no procedural assignment occurs. Multiple drivers
resolve on the net, and a delayed transition enters the scheduler's timed
update path.

Rewriting a no-delay gate as a binary expression would still lose net-driver
resolution, high impedance and source-to-destination update behavior. A
primitive array and a generate-created primitive add elaborated instance
storage, while strength and delay forms require further metadata. No second
scheduler or fake scalar assignment is introduced to make these cases appear
pure.

The current admission therefore stays explicit:

* procedural scalar/packed assignments and the existing continuous-assignment
  boundaries retain their current contracts;
* built-in primitive gates, conditional gates, switches, pull sources and
  primitive arrays remain `PrimitiveInstanceSymbol:PrimitiveInstance`; and
* a future primitive rung must first supply driver storage, four-state
  resolution, strength and delay publication through the existing scheduler.

## 2026-10-21 census and decision

The fresh 22,043-path census records
`PrimitiveInstanceSymbol:PrimitiveInstance` in **1,053** files: **543** are
primitive-only and **510** co-occur with another wall. The repricer walks the
frontend's concrete primitive instances in the 543 sole files and finds **681**
instances:

| primitive family | instances |
|---|---:|
| logic gates (`and/or/xor/xnor/nand/nor/not/buf`) | 302 |
| conditional gates (`bufif`/`notif`) | 99 |
| MOS switches (`nmos/pmos/cmos/rcmos/rnmos/rpmos`) | 130 |
| tran switches (`tran`/`rtran`, conditional variants) | 76 |
| pull sources (`pullup/pulldown`) | 74 |

The rows include **120** instances with a delay and **561** without, plus
primitive arrays and generate-created instances. No primitive family is
independently safe in the current store: even a no-delay logic gate requires
continuous publication and net resolution. All primitive instances therefore
remain loud until a scheduler-facing driver representation exists. Reproduce
the table with:

```text
python3.9 extractors/sv/primitive_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reads each source in process and writes no envelope beside the
corpus. Its primitive-shape counts are telemetry, not a new driver model.
