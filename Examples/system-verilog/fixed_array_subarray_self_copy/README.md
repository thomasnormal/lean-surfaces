# Fixed-array subarray self-copy

This fixture covers an exact blocking self-copy of one constant row in a fixed
multidimensional integral array. It has no observable store effect, so the
extractor emits `Empty`; nonblocking and overlapping copies remain loud.
