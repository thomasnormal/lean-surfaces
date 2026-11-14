// Conditional generate constructs inside generate loops (IEEE 1800-2023 §27.5): the arm a loop iteration instantiates
// depends on the genvars. `s[i]` takes the carry-in at bit 0 and `b[i-1]` above it; `g` is a three-level prefix-OR
// whose node `i` of level `l` combines with node `i - l - 1` where that exists (a condition on both genvars); `y` is
// an `else if` chain comparing by `==` and `!=`.
module gen_if #(parameter int N = 4) (
  input  logic [N-1:0]      a, b,
  input  logic              cin,
  output logic [N-1:0]      s,
  output logic [3:0][N-1:0] g,
  output logic [N-1:0]      y
);
  genvar i, l;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      if (i >= 1) begin : g_hi
        assign s[i] = a[i] ^ b[i - 1];
      end else begin : g_lo
        assign s[i] = a[i] ^ cin;
      end
    end
    for (i = 0; i < N; i++) begin : g_in
      assign g[0][i] = a[i] & b[i];
    end
    for (l = 0; l < 3; l++) begin : g_lvl
      for (i = 0; i < N; i++) begin : g_node
        if (i >= l + 1) begin : g_op
          assign g[l+1][i] = g[l][i] | g[l][i - l - 1];
        end else begin : g_pass
          assign g[l+1][i] = g[l][i];
        end
      end
    end
    for (i = 0; i < N; i++) begin : g_out
      if (i == 0) begin : g_first
        assign y[i] = g[3][i];
      end else if (i != N - 1) begin : g_mid
        assign y[i] = g[3][i] ^ g[3][i - 1];
      end else begin : g_last
        assign y[i] = g[3][i] & a[0];
      end
    end
  endgenerate
endmodule
