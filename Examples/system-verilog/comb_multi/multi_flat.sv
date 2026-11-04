// an always_comb body of TWO windows without a generate loop: `y` is a default with an override, `z` a second window
module multi_flat (input logic [3:0] a, b, input logic e, output logic [3:0] y, z);
  always_comb begin
    y = a;
    if (e) y = b;
    z = a ^ b;
  end
endmodule
