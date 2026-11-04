# String case conversion comparisons

IEEE 1800-2023 §§6.16.4–6.16.5 define `toupper()` and `tolower()` as pure
string transformations. This fixture compares the exact ASCII result and
checks that nonalphabetic characters remain unchanged.
