module neg_two_targets (input logic [1:0] s, input logic [3:0] a, b, output logic [3:0] y, output logic [3:0] z);
  always_comb begin
    case (s)
      2'd1: y = a;
      default: z = b;
    endcase
  end
endmodule
