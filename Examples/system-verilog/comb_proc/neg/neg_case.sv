// WP-G negative fixture neg_case: a case statement (outside the first fragment)
module neg_case #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0]   c;
  logic [N-1:0] p, u;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign p[i] = a[i] ^ b[i];
      always_comb begin
        case (p[i])
          1'b1: c[i+1] = c[i];
          default: c[i+1] = a[i];
        endcase
      end
      assign s[i] = p[i] ^ c[i];
    end
  endgenerate
  assign cout = c[N];
endmodule
