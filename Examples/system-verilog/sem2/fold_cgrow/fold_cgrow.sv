// Round 3 repair: constant contexts WIDER than at the default point. At the
// default N = 8 the comparisons below run at 32 bits (the int operand's
// width) and `U` is widened to 32; at N = 40 `U` is 2^32 and every
// operation runs at 40 bits (IEEE 1800-2023 11.6.1) — the constant tier
// used to truncate `U` to the default point's 32 bits (U > 5 false,
// U + 1 == 1 true, U >> 1 = 0).
module fold_cgrow #(parameter int N = 8, parameter logic [N-1:0] U = 33'h1_0000_0000) (
  input  logic        i,
  input  logic [31:0] a,
  output logic        o1,
  output logic        o2,
  output logic [31:0] o3
);
  localparam int L2 = U >> 1;
  if (U > 5) begin : g1
    assign o1 = i;
  end else begin : g0
    assign o1 = ~i;
  end
  if (U + 1 == 1) begin : h1
    assign o2 = i;
  end else begin : h0
    assign o2 = ~i;
  end
  assign o3 = L2 ^ a;
endmodule
