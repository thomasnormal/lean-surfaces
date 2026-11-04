# Finite associative-array delete history

Blocking `delete(key)` and whole-array `delete()` calls now replay through
finite literal-key associative-array history. A key delete restores the
element default and clears its presence bit; a whole-array delete clears every
known cell. Later `exists`, element reads, and `num()`/`size()` observations see
the deletion. Dynamic keys, aliases, timed/control-dependent calls, and
unknown aggregate operations remain loud.
