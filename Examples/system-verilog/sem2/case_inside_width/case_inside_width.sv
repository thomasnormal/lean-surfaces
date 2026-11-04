// `case … inside` compares the subject with each item PAIRWISE (IEEE
// 1800-2023 §12.5.4, §11.4.13), so one common width is exact only when no
// item is wider than the subject; here the unsized `4` (32 bits) is wider
// than the 2-bit `a`. Refused by the instantiation (`Case:inside-width`).
// (Icarus 12.0 does not parse `case … inside`.)
module case_inside_width #(parameter int N = 2) (
  input  logic [N-1:0] a,
  output logic         o
);
  always_comb begin
    case (a) inside
      4:       o = 1'b1;
      default: o = 1'b0;
    endcase
  end
endmodule
