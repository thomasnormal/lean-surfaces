# Conditional unpacked struct self-alias

A blocking whole-struct conditional assignment may read the destination in one
branch. The extractor lowers each integral field to a ternary, preserving the
source value for that field before its store. Nonblocking self-alias branches
remain loud; ordinary distinct-source conditionals already use this lowering.
