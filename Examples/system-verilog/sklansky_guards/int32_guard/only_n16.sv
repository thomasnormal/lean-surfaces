module add_n #(parameter int N = 16) (input logic [N-1:0] a,b, input logic cin, output logic [N-1:0] s, output logic cout);
logic [N:0] c;
assign c[0] = cin;
genvar i;
generate
 if (N == 16) begin : g_ripple
  for (i = 0; i < N; i++) begin : g_bit
   assign s[i] = a[i] ^ b[i] ^ c[i];
   assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
  end
  assign cout = c[N];
 end else begin : g_cheap
  assign s = a ^ b;
  assign cout = 1'b0;
 end
endgenerate
endmodule
