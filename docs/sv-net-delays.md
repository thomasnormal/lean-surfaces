# Net delays — repricing boundary

IEEE §§10.3.3, 4.9.1 and 28.16 attach delays to nets and to
declaration-time continuous assignments. A net delay schedules every value
transition through the net's drivers; one, two or three values select common,
rise/fall, or rise/fall/turn-off delays. Min:typ:max tuples and four-state
transitions select a delay at publication time. A delay written on a
declaration-time continuous assignment belongs to that assignment and is not
automatically added to the net delay.

## Why net delays remain a boundary

The public envelope has no delayed net driver, transition queue, inertial
cancellation/descheduling state, rise/fall/turn-off selector or min:typ:max
choice. Lowering a delayed net to an immediate continuous assignment exposes
intermediate pulses and changes the ordering of later updates. The tier
therefore keeps `NetSymbol:delay` loud, including declaration-time continuous
assignment delays, and introduces no second scheduler.

## 2026-10-22 census and decision

The fresh 22,043-path census records `NetSymbol:delay` in **27** files:
**21** are net-delay-only and **6** co-occur with another wall. Repricing the
sole files finds **22** spans: all are delayed nets, **8** are declaration-time
continuous-assignment forms, **9** specify rise/fall values, **2** specify a
turn-off value, **1** uses min:typ:max, **3** are vectors, **4** exercise
four-state `z` transitions, **3** exercise inertial cancellation or
rescheduling, **5** compare net and continuous-assignment delay placement and
**2** are chapter-37 type forms (features overlap).

Reproduce the table with:

```text
python3.9 extractors/sv/net_delay_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it reports declaration and transition shapes
without scheduling a publication or choosing a delay value.
