# Fixed-array `%p` diagnostics

This fixture covers the narrow self-check slice where a one-dimensional fixed
integral array is rendered as a `%p` diagnostic after a pure assignment pattern.
The array remains represented by its existing flattened cells; dynamic, nested,
and effectful aggregate values stay outside the tier.
