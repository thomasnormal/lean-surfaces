# Discarded pure `$rtoi`

The legacy self-check tier erases discarded `$rtoi` calls when the real
operand is source-pure. Read-only real names, literals, and nested pure math
calls are admitted; effectful or unsupported operands and value-position
conversions remain loud.
