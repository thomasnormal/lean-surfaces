# Static fixed-array continuous copy

This fixture covers IEEE 1800-2023 §7.6 for a fixed unpacked array whose
complete literal declaration initializer never changes.  The legacy
self-check envelope has one scalar cell per array element, so the continuous
assignment is lowered to one time-zero write per destination cell.  The
source and destination ranges have opposite directions to pin ordinal
correspondence.  A source with later writes, a dynamic source, or a live
continuous driver remains loud.
