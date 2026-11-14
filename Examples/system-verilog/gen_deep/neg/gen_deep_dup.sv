// Two blocks with the same label at the same depth (`g_b` under `g_x` and under `g_y`, each holding one site): their
// sites would share an identity (label, position, depth), which the structural check refuses.
module gen_deep_dup #(parameter int N = 4) (
  input  logic [N-1:0]        a,
  output logic [1:0][N-1:0]   z
);
  genvar i, j;
  generate
    for (i = 0; i < 1; i++) begin : g_x
      for (j = 0; j < N; j++) begin : g_b
        assign z[0][j] = a[j];
      end
    end
    for (i = 0; i < 1; i++) begin : g_y
      for (j = 0; j < N; j++) begin : g_b
        assign z[1][j] = a[j];
      end
    end
  endgenerate
endmodule
