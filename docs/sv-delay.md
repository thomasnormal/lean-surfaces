# Constant procedural delay controls

The scheduler-facing envelope admits a narrow, explicit subset of IEEE
1800-2023 §9.4 delay controls: a known nonnegative integral-literal `#d`
below 2^64, with its original statement body. The extractor records it as
`{"kind": "Delay", "amount": d, "body": ...}`. Ingestion lowers it to
the existing delay checkpoint followed by the original body.

The timed loader admits one or more initial bodies and schedules them in Active
at time zero in source order. Time is measured in that module's time-unit ticks, not an
inferred physical unit. The
existing retained-continuation stepper executes the statements before the
control, stores the remaining body, and turns a positive delay into an
absolute timer registration. Advancing time and delivering the timer puts the
same process back in Active; no source prefix is rerun and no continuation is
reconstructed.

The time-zero self-check executor deliberately remains loud on `Delay`: it
has no scheduler and therefore cannot silently claim a timed program ran.
The scheduler path delivers zero-delay `#0` through the Inactive region of
the same time slot, preserving the retained continuation and prior effects.
Dynamic or arithmetic delay expressions, negative or unknown
values, real/time-literal conversions, symbolic delay extraction, event
controls, continuous-assignment delays, and other process shapes remain loud.
This is a source-to-retained-continuation bridge, not an automatic time-wheel
driver or a claim of complete timed simulation.
