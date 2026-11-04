# Case-inside array widening

The legacy self-check tier admits a fixed unpacked integral array as a
`case (...) inside` item when each element can be widened to the subject's
integral width. Signed elements are sign-extended and unsigned elements are
zero-extended before the membership comparison, as required by IEEE
1800-2023 §12.5.4.

The existing scalar `inside` lowering supplies the first-match case chain;
dynamic arrays, aggregate elements, effectful selectors, and unsupported
width conversions remain loud.
