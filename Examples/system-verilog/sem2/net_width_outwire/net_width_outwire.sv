// Round 6 repair (H1, lane A, 2026-10-29): a NET formal fed by a bare,
// NARROWER NET actual that is an OUTPUT port of the instantiating module: an
// `output wire` and an implicit-type `output` are nets (IEEE 1800-2023
// 23.2.2.3), like an `input` port. IEEE 1800-2023 23.3.3 / 10.7 zero-extend
// the actual; Xcelium 24.03-s004 binds the nets bit for bit and leaves the
// formal's high bits undriven (z, warning CUVMPW). The extractor marks the
// connection (`"net": true`), so `PortConn:net-width` is the guard. Since
// WP-PROC N1/N2 (2026-11-01) the symbolic tier recovers the dimensions of the
// net outputs and declares each (one continuous driver per bit) as the
// variable it assigns, so the row reaches `PortConn:net-width` and the guard
// fires; before, it stopped earlier (`unrecoverable packed dimensions`, then
// `PortSymbol:net-z`). The explicitly typed outputs (`output logic`,
// `output reg`) are variables and stay admitted: see net_width_outvar.
module nwo_child (
  input  logic [5:0] i,
  output logic [5:0] p
);
  assign p = i;
endmodule

module net_width_outwire (
  input  logic [1:0] s,
  output wire  [1:0] ow,   // output wire: a net
  output       [1:0] oi,   // implicit-type output: a net
  output logic [5:0] pw,
  output logic [5:0] pi
);
  assign ow = s;
  assign oi = ~s;
  nwo_child uw (.i(ow), .p(pw));
  nwo_child ui (.i(oi), .p(pi));
endmodule
