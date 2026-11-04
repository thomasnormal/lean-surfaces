# Plain user-defined nettypes — bounded admission

The legacy self-check tier admits a user-defined nettype whose data type is a
four-state integral scalar or descending packed vector and whose declaration
has no resolution function. The nettype declaration is compile-time metadata;
an un-driven declaration using it lowers to a flat net initialized with
high-impedance bits. The `user_nettype` fixture covers scalar and vector
observations.

## Remaining boundary

A resolution function supplies the net's driver-combination semantics, and a
continuous driver supplies runtime state. The legacy envelope has neither, so
those forms remain explicit `NetSymbol:UserDefined` or `NetType:NetType`
refusals. Two-state, aggregate, dynamic, and non-integral nettype data also
remain outside the flat representation.
