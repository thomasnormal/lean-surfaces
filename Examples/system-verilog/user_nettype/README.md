# Plain user-defined nettypes

The legacy self-check tier lowers a user-defined nettype with an integral,
four-state data type and no resolution function when its declaration is
un-driven. The named nettype is compile-time metadata; each admitted scalar or
packed vector becomes a flat cell initialized to high impedance. Resolution
functions and continuous drivers remain loud.

The fixture checks scalar and packed-vector nettypes.
