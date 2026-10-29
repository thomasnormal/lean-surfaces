// A three-dimensional packed array: element targets at depth 2 from a
// `+:` part with a genvar-expression base, reads at depths 1-3 and a part
// select of the middle dimension (sv-0.2 `ArraySel`).
module array_3d (
  input  logic [23:0] src,
  output logic [23:0] m_flat,
  output logic [3:0]  e12,
  output logic [11:0] row0,
  output logic [7:0]  part,
  output logic        top_bit
);
  logic [1:0][2:0][3:0] m;
  genvar i, j;
  for (i = 0; i < 2; i++) begin : g_i
    for (j = 0; j < 3; j++) begin : g_j
      assign m[i][j] = src[(i*3 + j)*4 +: 4];
    end
  end
  assign m_flat  = m;
  assign e12     = m[1][2];
  assign row0    = m[0];
  assign part    = m[1][1:0];
  assign top_bit = m[0][2][3];
endmodule
