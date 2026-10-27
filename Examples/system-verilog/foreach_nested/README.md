# Multidimensional fixed-array `foreach`

This fixture binds both dimensions of a finite unpacked integral array in a
`foreach` loop. The extractor lowers each dynamic element read to the existing
flat leaf cells, and the self-check transcript is `sum=21`. Incomplete,
dynamic, queue, aggregate, and effectful array forms remain loud.
