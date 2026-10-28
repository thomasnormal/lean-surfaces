# Finite associative-array count history

For a finite source-pure associative array whose observed keys are literal
integral or ASCII string keys, `num()` and `size()` replay the exact number of
keys written before the query. Repeated writes do not increase the count.
Dynamic keys, aliases, whole-array operations, deletes, and other methods
remain loud.
