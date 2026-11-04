# Symbolic signed 2-state declarations

This fixture exercises the `sv-0.2` symbolic path for signed `bit` scalar and
packed-vector declarations. The declaration metadata retains both
`signed: true` and `two_state: true`; signed comparison is lowered to the
semantic tier's two's-complement comparison, and unknown input bits are
squashed at the 2-state boundary.
