# Parameter-sized unpacked input port

This clean-room fixture retains `input logic [W-1:0] a [N]` and genvar-indexed
NBA writes into `s[N]`. The current MemE entry refuses generated processes
before execution because it has no generate walker; this avoids silently
dropping the generated writes. The simulator rows remain pinned for the next
implementation slice.
