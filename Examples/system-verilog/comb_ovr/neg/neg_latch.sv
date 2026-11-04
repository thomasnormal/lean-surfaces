// no default before the override: a latch
module neg_latch (input logic [3:0] a, input logic e, output logic [3:0] y);
  always_comb begin
    if (e) y = a;
  end
endmodule
