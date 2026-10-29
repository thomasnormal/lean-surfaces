// Round 6 repair (H1, lane A, 2026-10-29): a NET formal fed by a bare, NARROWER
// NET actual that is an OUTPUT port of the instantiating module: an `output
// wire` and an implicit-type `output` are nets (IEEE 1800-2023 23.2.2.3).
// IEEE 1800-2023 23.3.3 / 10.7 zero-extend the actual; Xcelium 24.03-s004
// binds the nets bit for bit and leaves the formal's high bits undriven (z,
// warning CUVMPW). The extractor marks the connection (`"net": true`), so
// `PortConn:net-width` is the intended guard; TODAY the model refuses this
// design earlier, loudly (`assign target 'ow' undeclared`: the symbolic tier
// does not declare a net output port; a vector one is refused as
// "unrecoverable packed dimensions", see net_width_outwire). The explicitly
// typed outputs (`output logic`, `output reg`) are variables and stay
// admitted: see net_width_outvar1.
module nwo_child4 (
  input  logic [3:0] i,
  output logic [3:0] p
);
  assign p = i;
endmodule

module net_width_outwire1 (
  input  logic       s,
  output wire        ow,   // output wire: a net
  output             oi,   // implicit-type output: a net
  output logic [3:0] pw,
  output logic [3:0] pi
);
  assign ow = s;
  assign oi = ~s;
  nwo_child4 uw (.i(ow), .p(pw));
  nwo_child4 ui (.i(oi), .p(pi));
endmodule
