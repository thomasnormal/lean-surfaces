// the override writes another window of the same signal
module neg_otherwindow (input logic [3:0] a, input logic e, output logic [3:0] y);
  always_comb begin
    y[0] = a[0];
    if (e) y[1] = a[1];
  end
endmodule
