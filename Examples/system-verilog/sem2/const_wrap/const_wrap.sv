// Elaboration-time constant select labels built from operands NARROWER than
// 32 bits (verifier probes ps_wrap/ps_wrap2, 2026-10-28). Every label is
// evaluated at its self-determined width and signedness (IEEE 1800-2023
// §11.6, §11.8): `K + 3'd4` is 3-bit unsigned arithmetic and wraps, while
// `K + 4` (an unsized operand) widens K to 32 bits first. The same rule
// decides the generate-if condition. Rows: harness/sv/cases2.json
// `const_wrap*` (K and U swept; Icarus 12.0 and Yosys 0.53 agree on every
// value). K = 2 and K = 3 reverse the `[msb:lsb]` selects below (the
// labels wrap past each other) and are refused, not rows.
module const_wrap #(parameter logic [2:0] K = 3'd5,
                    parameter logic [3:0] U = 4'd0,
                    parameter int unsigned UI = 3) (
  input  logic [15:0] v,
  input  logic [19:4] nz,
  input  logic [7:0]  r,
  output logic [1:0]  o_add,
  output logic [1:0]  o_sub,
  output logic        o_bit,
  output logic        o_elem,
  output logic [1:0]  o_rng,
  output logic [1:0]  o_canon,
  output logic [1:0]  o_wide,
  output logic [3:0]  o_u,
  output logic        o_ui,
  output logic        o_gen,
  output logic [15:0] w_add
);
  assign o_add   = v[K + 3'd4 +: 2];
  assign o_sub   = v[K - 3'd6 -: 2];
  assign o_bit   = v[K + 3'd4];
  assign o_elem  = nz[K + 3'd7];
  assign o_rng   = nz[K + 3'd6 : K + 3'd5];
  assign o_canon = v[K + 3'd5 : K + 3'd4];
  assign o_wide  = v[K + 4 +: 2];
  assign o_u     = v[U - 4'd1 +: 4];
  assign o_ui    = v[UI + 1];
  if (K + 3'd4 > 3'd2) begin : g_t
    assign o_gen = 1'b1;
  end else begin : g_f
    assign o_gen = 1'b0;
  end
  always_comb begin
    w_add = '0;
    w_add[K + 3'd4 +: 2] = r[1:0];
  end
endmodule
