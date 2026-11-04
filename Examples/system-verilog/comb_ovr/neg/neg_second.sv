// a second unconditional assignment of the target
module neg_second (input logic [3:0] a, b, output logic [3:0] y);
  always_comb begin
    y = a;
    y = b;
  end
endmodule
