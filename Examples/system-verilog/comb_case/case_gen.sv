// WP-G S3a: a `case` in a generate loop at symbolic width, on a gate-tree subject (`s ^ a[i]`).
module case_gen #(parameter int N = 4) (input logic [N-1:0] a, b, input logic s, output logic [N-1:0] y);
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      always_comb begin
        case (s ^ a[i])
          1'd0: y[i] = b[i];
          default: y[i] = ~b[i];
        endcase
      end
    end
  endgenerate
endmodule
