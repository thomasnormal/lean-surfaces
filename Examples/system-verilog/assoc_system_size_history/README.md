# System `$size` on a finite associative-array history

IEEE 1800-2023 §20.7 and §7.11 define `$size` on an integral-key associative
array as its current number of allocated elements.  The self-check tier routes
source-pure finite histories through the same presence replay as `.num()` and
`.size()`, including compound writes and `delete`.  Dynamic keys, string-key
arrays, aliases, controls, and timed histories remain loud.
