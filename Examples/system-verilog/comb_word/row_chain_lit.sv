// WP-B2 gate 4a: the same chain over LITERAL dimensions: with a literal range every label, constant or not, is the legacy `BitSel`.
module row_chain_lit (
  input  logic [2:0] x,
  output logic [2:0] y
);
  logic [3:0][2:0] r;
  assign r[0] = x;
  for (genvar i = 0; i < 3; i++) begin : g
    assign r[i + 1] = ~r[i];
  end
  assign y = r[3];
endmodule
