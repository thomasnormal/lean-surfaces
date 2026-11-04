# Enum `.name()` comparisons

IEEE 1800-2023 §6.19.5 returns the declared spelling of an enum member from
`.name()`, and returns the empty string for an invalid value. This fixture
checks direct comparisons, names obtained from `first()`/`last()`, and the
invalid-value result.
