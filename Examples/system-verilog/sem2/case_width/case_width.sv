// A plain `case` compares at the widest of its subject and items (IEEE
// 1800-2023 §12.5): an unsized `-1` or `4` item is 32 bits, a narrower
// subject is zero-extended to it (verifier row `va2`; scratch `cs1`). The
// subject `a` is narrower than 32 bits at some points and wider at others.
module case_width #(parameter int N = 2) (
  input  logic [N-1:0] a,
  input  logic [1:0]   b,
  output logic         o1,
  output logic         o2,
  output logic         o3,
  output logic         o4,
  output logic         o5
);
  always_comb begin
    case (a)
      4:       o1 = 1'b1;
      default: o1 = 1'b0;
    endcase
    case (b)
      -1:      o2 = 1'b1;
      default: o2 = 1'b0;
    endcase
    case (b)
      2'b11:   o3 = 1'b1;
      default: o3 = 1'b0;
    endcase
    case (a)
      N:       o4 = 1'b1;
      default: o4 = 1'b0;
    endcase
    case (a)
      -1:      o5 = 1'b1;
      3'b111:  o5 = 1'b0;
      default: o5 = 1'b0;
    endcase
  end
endmodule
