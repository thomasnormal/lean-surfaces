// Round 3 repair: constant contexts NARROWER than at the default point. At
// N = 16 slang widened every literal operand below to 16 bits; at N = 8 the
// sum `8'd200 + 8'd100` wraps to 44 before `>> 5`, `/ 8'd3` and the generate
// comparison (IEEE 1800-2023 11.6.1: the operation width is the max of the
// operands and the target AT THAT POINT). The envelope keeps each widened
// literal as `Resize(16, literal)`, which the constant tier reads at the
// literal's own width.
module fold_lpshr #(parameter int N = 16) (
  input  logic [N-1:0] a,
  input  logic         i,
  output logic [N-1:0] o1,
  output logic [N-1:0] o2,
  output logic [N-1:0] o3,
  output logic         o4
);
  localparam logic [N-1:0] L4 = (8'd200 + 8'd100) >> 5;
  localparam logic [N-1:0] L5 = (8'd200 + 8'd100) / 8'd3;
  localparam logic [N-1:0] L6 = (8'd200 + 8'd100) > 9'd100;
  localparam logic [N-1:0] U = 8'd100;
  assign o1 = L4 ^ a;
  assign o2 = L5 ^ a;
  assign o3 = L6 ^ a;
  if (U + 8'd200 < 8'd50) begin : g1
    assign o4 = i;
  end else begin : g0
    assign o4 = ~i;
  end
endmodule
