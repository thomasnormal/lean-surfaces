// A 2-state `int` initialised by `/` (formerly a negative fixture): a correct ripple adder, plus a localparam that the
// sv_comb tactics read through its squashed operand (see ../comb_neg.lean, `lp_intdiv_comb`). The localparam is unused.
module lp_intdiv #(parameter int N = 8) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam int H = (N + 1) / 2;
  logic [N:0] c;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign s[i]   = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  assign cout = c[N];
endmodule
