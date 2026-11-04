// A ripple-carry adder whose sizes are LOCALPARAMS of the parameter N (the sv_comb tactics read a
// localparam as one more named constant: PROVING.md section 4). Every one of them is an integer
// constant expression of the parameter and the localparams before it: + - * by a literal, / and %
// by a literal. T equals N (2 * ceil(N/2) - N % 2), which `omega` knows from the definitions.
module lp_add #(parameter int N = 8) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam integer M = N - 1;          // affine
  localparam integer H = (N + 1) / 2;    // a quotient by a literal
  localparam integer R = N % 2;          // a remainder by a literal
  localparam integer T = 2 * H - R;      // from earlier localparams: T = N
  logic [T:0] c;                         // a localparam in a declaration
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < T; i++) begin : g_bit  // ... in a loop bound
      assign s[i]   = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  assign cout = c[M + 1];                // ... and in an index
endmodule
