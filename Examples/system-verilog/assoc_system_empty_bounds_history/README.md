# Empty associative-array low/high bounds

IEEE 1800-2023 §20.7 specifies all-`x` results from `$low` and `$high` when an
integral-key associative array has no allocated elements.  The self-check tier
admits this untouched-array result and composes it with `$isunknown` and the
zero `$size` query. Populated, dynamic, aliased, controlled, and timed histories
remain on their existing paths.
