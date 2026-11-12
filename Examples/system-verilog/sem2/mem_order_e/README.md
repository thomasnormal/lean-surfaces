# E memory order boundary

This clean-room design places `assign y = b` before `assign b = a` and keeps an
unpacked memory declaration beside the scalar drivers. IEEE 1800-2023 §§4.5 and
10.3 settle the continuous assignments independent of source order. The source
rows are retained here as a MemE risk receipt; this item makes no Kernel change
and makes no claim that the current one-pass profile has solved the ordering.
The Lean receipt guards the retained source process count, while `check.py`
compares both rows against the pinned simulators.
