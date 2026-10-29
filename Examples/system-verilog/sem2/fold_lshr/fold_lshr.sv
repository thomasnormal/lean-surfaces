// Round 3 repair: literal operands of a select index and of case items,
// widened by their context at the default N = 4. At N = 2 `s + 1'b1` wraps
// at 2 bits (IEEE 1800-2023 11.6.1) and the case compares at 2 bits; the
// envelope used to hold slang's 4-bit literals, so the model computed both
// at 4 bits. They are `Resize(4, literal)` now, read at the literal's own
// width.
module fold_lshr #(parameter int N = 4) (
  input  logic [N-1:0] s,
  input  logic [15:0]  v,
  output logic         o1,
  output logic         o2,
  output logic [1:0]   o3
);
  assign o1 = v[s + 1'b1];
  assign o2 = v[s + 2'd3];
  always_comb begin
    case (s)
      2'b11 + 2'b01: o3 = 2'd1;
      2'b10 + 2'b11: o3 = 2'd2;
      default: o3 = 2'd0;
    endcase
  end
endmodule
