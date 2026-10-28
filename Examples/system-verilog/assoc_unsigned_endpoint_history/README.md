# Unsigned packed integral associative-array endpoints

IEEE 1800-2023 §7.8.4 orders integral associative-array keys according to the
index type's signedness. The self-check tier now replays source-pure finite
arrays whose index is an unsigned packed integral alias, so `first` selects
`0` and `last` selects `15` from the keys `0`, `8`, and `15`. Dynamic keys,
controls, timing, and other aggregate forms remain loud.
