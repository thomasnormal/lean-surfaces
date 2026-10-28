# Pure integral operands for real conversions

The legacy self-check tier erases discarded `$itor`, `$bitstoreal`, and
`$bitstoshortreal` calls when their integral operands are source-pure. Reads
and pure integral operators are admitted; writes, timing, unsupported
expressions, and source operands with the wrong conversion width remain loud.
