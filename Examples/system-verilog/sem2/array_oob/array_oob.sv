// Constant selects past the END of a packed array's last element: reads
// give x in exactly the out-of-range bits, and a part-select target with
// an msb-side overhang writes only its in-range bits (IEEE 1800-2023
// 11.5.1). Both are the same under the per-dimension rule and under
// linearization, so every simulator agrees here (contrast array_oob_inner).
module array_oob (
  input  logic [3:0] a,
  output logic [7:0] m_flat,
  output logic [1:0] hi_read,
  output logic [3:0] over,
  output logic       beyond
);
  logic [1:0][3:0] m;
  always_comb begin
    m = 8'h00;
    m[0] = a;
    m[1][1:0] = ~a[1:0];
    m[1][5:2] = {2'b11, a[3:2]};
  end
  assign m_flat  = m;
  assign hi_read = m[1][5:4];
  assign over    = m[1][5:2];
  assign beyond  = m[1][6];
endmodule
