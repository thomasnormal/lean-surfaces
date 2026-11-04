// the multi-target form (stage S1b): the whole cell is one always_comb body
module add_proc_m #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0]   c;
  logic [N-1:0] p;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign p[i] = a[i] ^ b[i];
      always_comb begin
        if (p[i]) c[i+1] = c[i];
        else      c[i+1] = a[i];
        s[i] = p[i] ^ c[i];
      end
    end
  endgenerate
  assign cout = c[N];
endmodule
