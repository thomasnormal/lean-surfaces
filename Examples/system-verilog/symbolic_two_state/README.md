# Symbolic 2-state boundary

This fixture exercises the `sv-0.2` symbolic path for an unsigned `bit`
input and output.  The extractor keeps `two_state` on both declarations and
emits a `Squash2` at the assignment boundary.  `proof.lean` loads the
envelope, instantiates the semantic tier, and checks that an `x` input is
observed as zero at the output.
