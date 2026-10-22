# Specify blocks — repricing boundary

IEEE §§30–32 define `specify` blocks for module path delays, conditional and
edge-sensitive paths, timing checks, pulse controls and their diagnostics. A
path delay changes when a destination observes a source transition; a timing
check monitors event relationships and can update a notifier. These are
elaboration-time timing-model structures with scheduler-visible state.

## Why specify remains a boundary

The envelope has no path-delay graph, conditional path selection, timing-check
monitor, pulse state or notifier publication. Treating a specify block as a
procedural block, dropping its declarations, or selecting a fixed delay would
silently change both value propagation and diagnostic behavior. The public tier
therefore keeps every `SpecifyBlockSymbol:SpecifyBlock` loud and introduces no
second scheduler.

## 2026-10-22 census and decision

The fresh 22,043-path census records `SpecifyBlockSymbol:SpecifyBlock` in
**54** files: **28** are specify-only and **26** co-occurring. Repricing the
sole files finds **28** spans. Their overlapping source features are **14**
timing checks, **12** module paths, **14** edge-sensitive forms, **10** scalar
delays, **7** notifier references, **5** state-dependent paths, **4** indexed
terminals, **3** conditional paths, **3** polarity forms, **2** tuple delays,
**1** `ifnone` path, **1** illegal edge specification, **1** invalid concurrent
assertion and **1** invalid system task. Reproduce the table with:

```text
python3.9 extractors/sv/specify_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it reports source shapes without resolving a path,
running a timing monitor or scheduling notifier activity.
