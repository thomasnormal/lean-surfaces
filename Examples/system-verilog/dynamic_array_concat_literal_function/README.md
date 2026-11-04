# Literal-return function in a dynamic-array concatenation

This fixture covers the source-pure `get_value()` form of an unpacked
concatenation assigned to a dynamic array. The function has no output or
inout arguments and assigns its literal result through the implicit function
name. The extractor materializes that call as one scalar cell, so the
self-check transcript is `PASS`.

Calls whose result depends on state or whose body has effects remain loud.
