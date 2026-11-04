// a window written in two separate groups of statements: the second group of `y` comes after `z`
module neg_interleave (input logic [3:0] a, b, input logic e, output logic [3:0] y, z);
  always_comb begin
    y = a;
    z = b;
    if (e) y = b;
  end
endmodule
