// an `if/else` after the first statement
module neg_elsechain (input logic [3:0] a, b, c, input logic e, output logic [3:0] y);
  always_comb begin
    y = a;
    if (e) y = b; else y = c;
  end
endmodule
