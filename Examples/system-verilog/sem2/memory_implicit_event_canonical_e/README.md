# Implicit event control memory boundary

This clean-room fixture records the next canonical-memory wall after time-zero
initialization: `always @*` reads a source-shaped unpacked memory. The current
CoreMemExec entry refuses the implicit event process explicitly; simulator rows
are retained for the future sensitivity implementation.
