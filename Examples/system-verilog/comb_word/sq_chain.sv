// A `$clog2` localparam as the bound of a generate loop, with `*` in its body: L = $clog2(N) + 1 squarings of x
// modulo 2^N, a chain of rows r[i + 1] = r[i] * r[i], so y = x^(2^L) mod 2^N.
module sq_chain #(parameter int N = 4) (
  input  logic [N-1:0] x,
  output logic [N-1:0] y
);
  localparam integer L = $clog2(N) + 1;
  logic [L:0][N-1:0] r;
  assign r[0] = x;
  for (genvar i = 0; i < L; i++) begin : g
    assign r[i + 1] = r[i] * r[i];
  end
  assign y = r[L];
endmodule
