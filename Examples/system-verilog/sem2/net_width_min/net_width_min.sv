// Round 6 (Xcelium audit cluster H1, lane A, 2026-10-29): a NET formal fed by
// a bare, NARROWER net actual. `s` is an input port (a net, 23.2.2.3) and the
// formal `i` is a net (an input without `var`). IEEE 1800-2023 23.3.3 / 10.7
// read the connection as a continuous assignment that zero-extends `s`
// (`p = 000001` at s = 01); Icarus 12.0, Verilator 5.042, Yosys 0.53 and slang
// agree. Xcelium 24.03-s004 binds the two nets bit for bit and leaves the
// formal's high bits undriven: `p = zzzz01` (warning CUVMPW). The model
// refuses it (`PortConn:net-width`); see net_width_ok for the shapes every
// tool zero-extends.
module nw_child (
  input  logic [5:0] i,
  output logic [5:0] p
);
  assign p = i;
endmodule

module net_width_min (
  input  logic [1:0] s,
  output logic [5:0] p
);
  nw_child u (.i(s), .p(p));
endmodule
