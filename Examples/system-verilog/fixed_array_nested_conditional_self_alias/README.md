# Nested conditional fixed-array self-alias

A blocking conditional assignment over a multidimensional fixed unpacked array
can read the destination in one branch. Each ordinal cell is lowered to a
source-preserving ternary, even when the declared unpacked bounds differ.
Nonblocking self-alias branches remain loud because publication is
scheduler-visible.
