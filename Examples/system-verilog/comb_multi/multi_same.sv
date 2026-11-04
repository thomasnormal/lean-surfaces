// two windows of ONE signal in one `always_comb` body: `y[0]` and `y[1]` (the ordinals of the stable aliases follow source order)
module multi_same (input logic [1:0] a, b, output logic [1:0] y);
  always_comb begin
    y[0] = a[0] & b[0];
    y[1] = a[1] | b[1];
  end
endmodule
