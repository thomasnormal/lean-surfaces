// F3 differential design: unbased-unsized fills NESTED under an operator in
// input-port actuals narrower than the port, where the widened bits survive.
// A fill is as wide as its context (IEEE 1800-2023 §5.7.1) and a port
// connection is a continuous assignment (§23.3.3), so `a ^ '1` into a 4-bit
// port is {2'b11, ~a}: the model, Verilator 5.042 and Yosys 0.53 agree.
// Icarus 12.0 sizes the nested fill self-determined and zero-pads
// ({2'b00, ~a}) — the declared disagreement of row `hier_fill_ctx`.
module hfc_pass (
  input  logic [3:0] x,
  output logic [3:0] y
);
  assign y = x;
endmodule

module hier_fill_ctx (
  input  logic [1:0] a,
  input  logic [1:0] b,
  input  logic       s,
  output logic [3:0] xor1,
  output logic [3:0] or1,
  output logic [3:0] tern1,
  output logic [3:0] orx,
  output logic [3:0] xorz,
  output logic [3:0] ternz,
  output logic [3:0] and11,
  output logic [3:0] orb,
  output logic [3:0] cxor,
  output logic [3:0] ctern
);
  hfc_pass u_xor1  (.x(a ^ '1),          .y(xor1));
  hfc_pass u_or1   (.x(a | '1),          .y(or1));
  hfc_pass u_tern1 (.x(s ? '1 : a),      .y(tern1));
  hfc_pass u_orx   (.x(a | 'x),          .y(orx));
  hfc_pass u_xorz  (.x(a ^ 'z),          .y(xorz));
  hfc_pass u_ternz (.x(s ? 'z : a),      .y(ternz));
  hfc_pass u_and11 (.x('1 & '1),         .y(and11));
  hfc_pass u_orb   (.x((a ^ '1) | b),    .y(orb));
  hfc_pass u_cxor  (.x('1 ^ '0),         .y(cxor));
  hfc_pass u_ctern (.x(s ? '1 : '0),     .y(ctern));
endmodule
