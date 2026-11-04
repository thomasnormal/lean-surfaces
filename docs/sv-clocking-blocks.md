# Clocking blocks — repricing boundary

IEEE §14 defines clocking blocks as synchronization declarations. A clocking
event samples input clockvars and schedules output clockvar drives at defined
simulation regions; input and output skew move those sample and drive times.
Global and default clocking declarations also provide scope-wide clocking
references for assertion and sequence code.

## Why clocking blocks remain a boundary

The envelope has no clockvar sample/drive queues, skew representation, global
clocking scope or Preponed/Reactive region bridge. Treating a clocking block as
an ordinary event wait and variable declaration loses sampled values, delayed
drives and output-net driver initialization. The public tier therefore keeps
every `ClockingBlockSymbol:ClockingBlock` loud and adds no second scheduler.

## 2026-10-22 census and decision

The fresh 22,043-path census records `ClockingBlockSymbol:ClockingBlock` in
**562** files: **24** are clocking-only and **538** co-occurring. Repricing the
sole files finds **24** spans: **8** global declarations, **4** default
declarations, **8** input clockvar forms, **5** output clockvar forms, **4**
sequence/property-containing blocks, **5** nested event/control forms, **3**
generated placements, **1** skew declaration, **1** end-label and **1** unnamed
clocking block (features overlap). Reproduce the table with:

```text
python3.9 extractors/sv/clocking_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it reports declarations without sampling a
clockvar, scheduling a drive or selecting a simulation region.
