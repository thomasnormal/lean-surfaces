# Finite associative-array compound assignment history

IEEE 1800-2023 §10.4.1 operator assignments read and write one associative-array element.  When all selectors are literal or immutable literal-key bindings, the self-check tier replays those writes as flat cells.  `num()` and `size()` then observe the exact distinct-key presence count after the compound writes.  Dynamic selectors, aliases, control-dependent writes, and scheduled forms remain loud.
