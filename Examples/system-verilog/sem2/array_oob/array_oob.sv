// Constant selects past the END of a packed array's last element: reads
// give x in exactly the out-of-range bits, and a part-select target with
// an msb-side overhang writes only its in-range bits (IEEE 1800-2023
// 11.5.1). Both are the same under the per-dimension rule and under
// linearization (contrast array_oob_inner), so the model, Icarus 12.0 and
// Yosys 0.53 agree here. Xcelium 24.03-s004 does NOT: it treats a
// part-select that is only partly in range as wholly invalid (`over` reads
// all x and the overhanging write is dropped), against the LRM text
// (docs/sv-xcelium-audit.md, clusters P1 and P3).
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
