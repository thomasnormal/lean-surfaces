// Phase-2 probe: `unique case … inside` with `?` wildcard patterns
// (§12.5.4 — the decoder's dispatch style). Icarus cannot parse the
// construct; this case is Xcelium-verified only (recorded gap).
module t2_ci (
    input  logic [4:0] a,
    output logic [2:0] y
);
  always_comb begin
    unique case (a) inside
      5'b0001?: y = 3'd1;
      5'b001??: y = 3'd2;
      5'b1????: y = 3'd3;
      5'b00001: y = 3'd4;
      default:  y = 3'd0;
    endcase
  end
endmodule
