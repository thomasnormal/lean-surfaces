# Multidimensional fixed-array blocking self-copy

An exact blocking self-copy of a multidimensional fixed unpacked array is a
no-op: every flattened source cell is already the corresponding destination
cell. The extractor erases this assignment while preserving the initialized
values. Nonblocking, partial, overlapping, dynamic, and effectful copies stay
loud.
