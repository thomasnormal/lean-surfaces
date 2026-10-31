# Event lists — repricing boundary

IEEE §§9.4.2, 12.4 and 12.6 allow an event control to contain several event
expressions joined by `or` or comma. A process wakes when any listed event
occurs; edge descriptors select transitions, and `iff` filters the adjacent
event at occurrence time. The event expression is then re-armed as the same
process continuation.

## The retained event-list slice

The timed envelope now admits a plain `always` list with one or more scalar
identifier events, including the bare `always @(signal)` spelling. Each entry retains its `any`, `posedge`, or `negedge`
polarity, and the process stores the whole list while suspended. A publication
wakes it when any listed edge fires; completion re-arms the same body through
the existing Active/Inactive/NBA loop. This is one multi-event registration,
not a second scheduler.

`always_ff` lists continue to use the narrower asynchronous-reset forms.
Empty lists, `iff`, non-scalar expressions, and other clock/reset shapes remain
loud because they need guards or sequential rules that are not represented.

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
