# Conditional fixed-array self-alias

A blocking whole-array conditional assignment may read the destination in one
branch. Each fixed-array cell is lowered to a source-preserving ternary.
Nonblocking self-alias branches remain loud because publication is
scheduler-visible.
