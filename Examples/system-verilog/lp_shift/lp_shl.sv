// A ripple adder with a SHIFT in an unused localparam (`S = N << 1`, IEEE 1800-2023 §11.4.10). It used to be the negative
// fixture `lp_add/neg/lp_shift.sv` ("operator `<<` is outside the v1 fragment"); the localparam reading now has the
// shifts of an `int`, so the design is read as written.
module lp_shift #(parameter int N = 8) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam integer S = N << 1;
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
