# E memory order boundary

This clean-room design places `assign y = b` before `assign b = a` and keeps an
unpacked memory declaration beside the scalar drivers. IEEE 1800-2023 §§4.5 and
10.3 settle the continuous assignments independent of source order. The current
one-pass MemE profile refuses the shape with `Schedule:comb-source-order` rather
than returning the stale intermediate value. The Lean receipt also guards the
§6.8 two-state startup conversion.
