module neg_xitem (input logic [1:0] s, input logic [3:0] a, b, output logic [3:0] y);
  always_comb begin
    case (s)
      2'b1x: y = a;
      default: y = b;
    endcase
  end
endmodule
