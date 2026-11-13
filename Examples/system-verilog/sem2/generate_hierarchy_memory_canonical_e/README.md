# Canonical E generated child memory

This source-shaped receipt expands one generated child instance through the
existing `PDesign`/`PInst` hierarchy nodes. The child's unpacked storage stays
one canonical `MemState`, and its port connections become source-shaped
assignments under IEEE 1800-2023 §23.3.3. The startup row matches Icarus
Verilog 13.0 and readiness-gated Xcelium 24.03-s004. Later persistent-write
rows remain an explicit reduction-cost boundary for the function-backed
canonical store; no unmeasured result is claimed.
