# Event lists — repricing boundary

IEEE §§9.4.2, 12.4 and 12.6 allow an event control to contain several event
expressions joined by `or` or comma. A process wakes when any listed event
occurs; edge descriptors select transitions, and `iff` filters the adjacent
event at occurrence time. The event expression is then re-armed as the same
process continuation.

## Why event lists remain a boundary

The public wait representation admits one bare signal or one simple edge
event. It has no multi-event registration, per-event `iff` guard or retained
rearming state. Lowering an event list to the first signal, one edge, or a
single sequential wait changes which event wakes the process and how repeated
wakes behave. The public tier therefore keeps every
`TimedStatement:EventListControl` loud and adds no second scheduler.

## 2026-10-22 census and decision

The fresh 22,043-path census records `TimedStatement:EventListControl` in
**38** files: **24** are event-list-only and **14** co-occurring. Repricing the
sole files finds **25** spans: **21** `or` lists, **6** comma lists, **10** edge
events, **4** `iff` filters, **3** lists with at least three events, **4** block
bodies, **3** `always_ff` controls, **1** parenthesized list, **1** indexed
expression and **1** procedural assign/deassign (features overlap). Reproduce
the table with:

```text
python3.9 extractors/sv/event_list_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it reports event syntax without registering a
wait, choosing an event or advancing the scheduler.
