// Round 6 repair (H1 control, lane A, 2026-10-29): the scalar twin of
// net_width_outvar. An `output logic` and an `output reg` port are VARIABLES
// (IEEE 1800-2023 23.2.2.3, explicit data type), so a one-bit variable actual
// into a four-bit net formal is zero-extended by every tool and
// `PortConn:net-width` must NOT fire. Compare net_width_outwire1 (the same
// shape with net outputs: refused).
module nwo_child4 (
  input  logic [3:0] i,
  output logic [3:0] p
);
  assign p = i;
endmodule

module net_width_outvar1 (
  input  logic       s,
  output logic       ol,   // output logic: a variable
  output reg         orr,  // output reg:   a variable
  output logic [3:0] pl,
  output logic [3:0] pr
);
  assign ol = s;
  always_comb orr = ~s;
  nwo_child4 ul (.i(ol),  .p(pl));
  nwo_child4 ur (.i(orr), .p(pr));
endmodule
