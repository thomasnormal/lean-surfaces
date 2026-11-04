// Context-determined operand widths that depend on a parameter (IEEE
// 1800-2023 11.6.1, 11.8.2; verifier finding 2026-10-28): an operand
// NARROWER than the context is extended before the operator (`-a` at N = 2
// into 4 bits is 1110 for a = 10, not 0010), one WIDER is operated on at its
// own width and the result truncated (`v[1 +: N] + 4'd9` at N = 8 reads x
// in bit 8, which collapses the sum), a sized literal is extended to the
// width at THESE parameters (the self-determined `{a + 1'b1, 1'b0}` is
// N + 1 bits), and a comparison is as wide as its widest operand here.
// slang elaborates the envelope at the default N = 4, so its conversion
// nodes are those of N = 4. Rows: harness/sv/cases2.json `ctx_width*`.
module ctx_width #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [7:0]   v,
  input  logic [3:0]   b,
  output logic [3:0]   o_neg,   // -a
  output logic [3:0]   o_not,   // ~a
  output logic [3:0]   o_add,   // a + 4'd1
  output logic [3:0]   o_sneg,  // -v[0 +: N]
  output logic [3:0]   o_snot,  // ~v[0 +: N]
  output logic [3:0]   o_ov,    // v[1 +: N] + 4'd9
  output logic [3:0]   o_sub,   // b - v[0 +: N]
  output logic [3:0]   o_mul,   // (v[0 +: N] * 3) & b
  output logic [3:0]   o_and,   // (-a) & b
  output logic         o_eq,    // a == 4'd3
  output logic         o_lt,    // v[0 +: N] < 5'd17
  output logic [5:0]   o_cat    // {a + 1'b1, 1'b0}
);
  assign o_neg  = -a;
  assign o_not  = ~a;
  assign o_add  = a + 4'd1;
  assign o_sneg = -v[0 +: N];
  assign o_snot = ~v[0 +: N];
  assign o_ov   = v[1 +: N] + 4'd9;
  assign o_sub  = b - v[0 +: N];
  assign o_mul  = (v[0 +: N] * 3) & b;
  assign o_and  = (-a) & b;
  assign o_eq   = a == 4'd3;
  assign o_lt   = v[0 +: N] < 5'd17;
  assign o_cat  = {a + 1'b1, 1'b0};
endmodule
