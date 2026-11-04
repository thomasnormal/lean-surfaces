# Discarded pure floating math

The legacy self-check tier erases discarded real-valued math calls when the
existing source-purity walk accepts every operand. Literals, read-only names,
and nested pure math calls are admitted; updates, timing, unsupported
expressions, and value-position real calls remain loud.
