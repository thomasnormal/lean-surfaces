// Round 6 repair (H1 control, lane A, 2026-10-29): the narrower-actual shapes
// whose actual is an OUTPUT port declared with an explicit data type. Such a
// port is a VARIABLE (IEEE 1800-2023 23.2.2.3: with the explicit data_type
// syntax the port kind defaults to variable), although slang reports it with
// the same `VariablePortHeader` and no `var` as an `input logic` net. Every
// tool zero-extends a variable actual into the wider net formal, Xcelium
// 24.03-s004 included, so `PortConn:net-width` must NOT fire. Compare
// net_width_outwire (a NET output actual: refused) and net_width_ok.
module nwo_child (
  input  logic [5:0] i,
  output logic [5:0] p
);
  assign p = i;
endmodule

module net_width_outvar (
  input  logic [1:0]     s,
  output logic [1:0]     ol,   // output logic: a variable
  output reg   [1:0]     orr,  // output reg:   a variable
  output var logic [1:0] ov,   // output var:   a variable
  output logic [5:0]     pl,
  output logic [5:0]     pr,
  output logic [5:0]     pv
);
  assign ol = s;
  always_comb orr = ~s;
  assign ov = s ^ 2'b01;
  nwo_child ul (.i(ol),  .p(pl));
  nwo_child ur (.i(orr), .p(pr));
  nwo_child uv (.i(ov),  .p(pv));
endmodule
