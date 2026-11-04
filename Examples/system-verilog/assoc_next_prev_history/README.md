# Finite associative-array `next` and `prev`

This fixture covers IEEE 1800-2023 §7.9.4–7.9.5 for integral-key finite
associative arrays. Source-pure literal keys use the existing flat presence
cells; `next(index)` selects the least present key greater than `index`, and
`prev(index)` selects the greatest present key less than `index`. A failed
lookup returns zero and leaves the index unchanged.
