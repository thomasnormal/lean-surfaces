// F3 differential design: unbased-unsized fills in input-port actuals
// NARROWER than the port where every tool agrees. A bare fill fills the
// port; a fill whose widened bits are masked (`a & '1`, `s ? '0 : a`,
// `(a ^ '1) & b`) leaves zeros above the actual in the LRM reading and in
// the self-determined, zero-padded one alike. (The shapes where Icarus 12.0
// alone pads a nested fill with zeros are `hier_fill_ctx`.)
module hf_pass (
  input  logic [3:0] x,
  output logic [3:0] y
);
  assign y = x;
endmodule

module hier_fill (
  input  logic [1:0] a,
  input  logic [1:0] b,
  input  logic       s,
  output logic [3:0] f1,
  output logic [3:0] f0,
  output logic [3:0] fx,
  output logic [3:0] fz,
  output logic [3:0] and1,
  output logic [3:0] andx,
  output logic [3:0] t0,
  output logic [3:0] nest
);
  hf_pass u_f1   (.x('1),            .y(f1));
  hf_pass u_f0   (.x('0),            .y(f0));
  hf_pass u_fx   (.x('x),            .y(fx));
  hf_pass u_fz   (.x('z),            .y(fz));
  hf_pass u_and1 (.x(a & '1),        .y(and1));
  hf_pass u_andx (.x(a & 'x),        .y(andx));
  hf_pass u_t0   (.x(s ? '0 : a),    .y(t0));
  hf_pass u_nest (.x((a ^ '1) & b),  .y(nest));
endmodule
