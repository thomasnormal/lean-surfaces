# Discarded pure real-to-bits conversions

The legacy self-check tier erases discarded `$realtobits` and
`$shortrealtobits` calls when their real operands are source-pure. Read-only
real names, literals, and nested pure math calls are admitted; effectful or
unsupported operands and value-position conversions remain loud.
