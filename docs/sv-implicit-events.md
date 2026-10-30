# Implicit event controls — admitted `@*` path

IEEE §9.4.2 and §12.6.4 define `@*`/`@(*)` by deriving a sensitivity set from
the variables read by the controlled statement. The process waits for any
change in that inferred set, executes the body, and re-arms the same implicit
control. Reads in branches, case items, indexes and concatenations participate
in the set, while identifiers used only by nested timing controls are excluded.

## The retained sensitivity path

`AlwaysImplicit` stores the inferred read set and retained body in the same
timed process table as the other concurrent processes. It runs once at time
zero, becomes dormant, and wakes when a read signal changes. Blocking writes
publish after each statement and NBA commits publish through the same edge
queue, so two changes in one time slot are observable without a second
scheduler. Empty bodies remain loud, as do event lists, `iff`, and level waits
that require a different admission rule.

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
