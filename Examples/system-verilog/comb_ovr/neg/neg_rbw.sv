// read before write: the second statement reads the target it wrote (outside the fragment: SSA is not modelled)
module neg_rbw (input logic [3:0] a, b, input logic e, output logic [3:0] y);
  always_comb begin
    y = a;
    if (e) y = y ^ b;
  end
endmodule
