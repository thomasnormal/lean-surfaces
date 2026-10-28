# Dynamic outer-array targets

A sampled `new[N]` dynamic array whose elements have fixed unpacked
integral dimensions is flattened into the existing cell state. Blocking writes
through dynamic selectors are expanded into mutually exclusive cell branches;
aggregate storage and unsampled or nested-dynamic shapes remain loud.
