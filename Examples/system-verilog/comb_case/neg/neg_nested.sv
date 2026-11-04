module neg_nested (input logic [1:0] s, input logic [3:0] a, b, output logic [3:0] y);
  always_comb begin
    case (s)
      2'd1: if (a[0]) y = a; else y = b;
      default: y = b;
    endcase
  end
endmodule
