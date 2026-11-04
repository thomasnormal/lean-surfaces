// clmul, one level of Karatsuba, any N >= 1: H = ceil(N/2); a and b are zero-padded to 2H+1 bits (ap, bp; only the
// low 2H are read; the vectors are one bit longer so that the pad loop g_pz never has zero iterations at the default
// N). L = aL (x) bL, Hh = aH (x) bH, M = (aL ^ aH) (x) (bL ^ bH) are three H x H carry-less arrays, the reference's
// shape, read directly by the combination layer: pf = L + x^H (M ^ L ^ Hh) + x^2H Hh and p = pf[2N-2:0], where bit k
// of an array's product is column 0 of row k (k < H) and the top row at column k - H + 1 (k >= H).
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  localparam integer H = (N + 1) / 2;
  logic [2*H:0]        ap, bp;
  logic [H-1:0][H-1:0] rl, rh, rm;
  logic [4*H-2:0]      pf;

  genvar i, j;
  generate
    for (i = 0; i < N; i++) begin : g_pin
      assign ap[i] = a[i];
      assign bp[i] = b[i];
    end
    for (i = 0; i < 2*H+1-N; i++) begin : g_pz
      assign ap[N+i] = 1'b0;
      assign bp[N+i] = 1'b0;
    end
    // l
    for (j = 0; j < H; j++) begin : g_l0
      assign rl[0][j] = ap[0] & bp[j];
    end
    for (i = 1; i < H; i++) begin : g_l
      for (j = 0; j < H-1; j++) begin : g_lb
        assign rl[i][j] = rl[i-1][j+1] ^ (ap[i] & bp[j]);
      end
      assign rl[i][H-1] = ap[i] & bp[H-1];
    end
    // h
    for (j = 0; j < H; j++) begin : g_h0
      assign rh[0][j] = ap[H+0] & bp[H+j];
    end
    for (i = 1; i < H; i++) begin : g_h
      for (j = 0; j < H-1; j++) begin : g_hb
        assign rh[i][j] = rh[i-1][j+1] ^ (ap[H+i] & bp[H+j]);
      end
      assign rh[i][H-1] = ap[H+i] & bp[H+H-1];
    end
    // m
    for (j = 0; j < H; j++) begin : g_m0
      assign rm[0][j] = (ap[0] ^ ap[H+0]) & (bp[j] ^ bp[H+j]);
    end
    for (i = 1; i < H; i++) begin : g_m
      for (j = 0; j < H-1; j++) begin : g_mb
        assign rm[i][j] = rm[i-1][j+1] ^ ((ap[i] ^ ap[H+i]) & (bp[j] ^ bp[H+j]));
      end
      assign rm[i][H-1] = (ap[i] ^ ap[H+i]) & (bp[H-1] ^ bp[H+H-1]);
    end
    // pf = L + x^H (M ^ L ^ Hh) + x^2H Hh
    for (i = 0; i < H; i++) begin : g_c0
      assign pf[i] = rl[i][0];
    end
    for (i = 0; i < H-1; i++) begin : g_c1
      assign pf[H+i] = rl[H-1][i+1] ^ (rm[i][0] ^ rl[i][0] ^ rh[i][0]);
    end
    for (i = 0; i < 1; i++) begin : g_cm
      assign pf[2*H-1+i] = rm[H-1][0] ^ rl[H-1][0] ^ rh[H-1][0];
    end
    for (i = 0; i < H-1; i++) begin : g_c2
      assign pf[2*H+i] = rh[i][0] ^ (rm[H-1][i+1] ^ rl[H-1][i+1] ^ rh[H-1][i+1]);
    end
    for (i = 0; i < H; i++) begin : g_c3
      assign pf[3*H-1+i] = rh[H-1][i];
    end
    for (i = 0; i < 2*N-1; i++) begin : g_out
      assign p[i] = pf[i];
    end
  endgenerate
endmodule
