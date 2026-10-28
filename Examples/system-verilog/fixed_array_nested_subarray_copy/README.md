# Nested fixed-array subarray copy

A constant subarray reference such as `source[1]` can fill a nested fixed
unpacked destination when both sides have the same ordinal leaf count. The
lowering pairs flattened cells in declaration order; overlapping same-root
copies remain loud.
