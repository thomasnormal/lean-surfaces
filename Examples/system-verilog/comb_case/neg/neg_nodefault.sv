module neg_nodefault (input logic [1:0] s, input logic [3:0] a, b, output logic [3:0] y);
  always_comb begin
    case (s)
      2'd0: y = a;
      2'd1: y = b;
    endcase
  end
endmodule
