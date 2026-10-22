# Implicit event controls — repricing boundary

IEEE §9.4.2 and §12.6.4 define `@*`/`@(*)` by deriving a sensitivity set from
the variables read by the controlled statement. The process waits for any
change in that inferred set, executes the body, and re-arms the same implicit
control. Reads in branches, case items, indexes and concatenations participate
in the set, while identifiers used only by nested timing controls are excluded.

## Why implicit sensitivity remains a boundary

The envelope can represent fixed edge and bare-signal waits, but it has no
inferred read-set node or process rearming state. Treating `@*` as a fixed edge,
running it once, or treating every identifier in the source as sensitive would
change wakeups and same-time-slot behavior. Nested controls add a second
retained continuation, and body effects still use the existing scheduler.

The public tier therefore keeps every implicit event control loud. No source
order shortcut, guessed sensitivity list, or second scheduler is introduced;
the existing `Always` and `WaitEvent` contracts remain the dependencies for a
future lowering.

## 2026-10-22 census and decision

The fresh 22,043-path census records `TimedStatement:ImplicitEventControl` in
**53** files: **38** are implicit-control-only and **15** co-occur with another
wall. Repricing the sole files finds **38** spans: **29** use bare `@*`, **9**
use `@(*)`, **25** have block bodies, **14** contain case statements, **5**
contain indexed selects, **4** contain conditionals, **3** contain nested
controls, **3** contain concatenations and **1** contains a system call (rows
overlap). Reproduce the table with:

```text
python3.9 extractors/sv/implicit_event_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and does not infer or execute a sensitivity list.
