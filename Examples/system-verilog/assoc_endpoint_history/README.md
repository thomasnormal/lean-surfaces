# Finite associative-array endpoint history

Blocking assignments from integral-key associative-array `first(index)` and
`last(index)` now lower to a presence-priority chain. They return one and
update the index variable to the least or greatest present literal key; an
empty array returns zero and leaves the index unchanged. String-key endpoint
outputs and dynamic or unsupported histories remain loud.
