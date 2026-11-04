// Self-determined constant roots over a narrow signed parameter (round 4
// folds, verifier repros rf_lbl/rf_gen/rf_lp/rf_par): a select label, a
// generate condition, an untyped localparam and an untyped parameter
// default are evaluated at their OWN width at the point. slang's tree of
// `SB + 1'b1` at the default N = 8 is `Resize(8, SB) + Resize(8, 1'b1)`;
// reading those widths as a context made `v[SB + 1'b1]` read v[16] at N = 4,
// where Icarus 12.0 and the Yosys 0.53 netlist read v[0].
module fold_rself #(parameter int N = 8, parameter logic signed [N-1:0] SB = -1,
                    parameter Y = (SB + 1'b1) >> 1) (
  input  logic [31:0] v,
  output logic o1,
  output logic o2,
  output logic [3:0] o3,
  output logic [15:0] o4,
  output logic [15:0] o5);
  localparam X = (SB + 1'b1) >> 1;
  assign o1 = v[SB + 1'b1];
  assign o2 = v[(SB + 1'b1) >> 1];
  if (SB + 1'b1) begin : g1
    assign o3 = v[3:0];
  end else begin : g0
    assign o3 = ~v[3:0];
  end
  assign o4 = X;
  assign o5 = Y;
endmodule
