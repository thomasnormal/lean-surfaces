# Disjoint fixed-array subarray copy

This fixture covers a blocking copy from one constant row to another row of
one fixed multidimensional integral array. The rows do not overlap, so the
existing cellwise lowering reads the complete source row before any target
cell can affect a source read. An overlapping or otherwise dynamic subarray
copy remains loud.
