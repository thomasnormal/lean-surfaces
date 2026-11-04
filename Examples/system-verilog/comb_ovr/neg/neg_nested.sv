// a begin..end with several statements as a statement of a block
module neg_nested (input logic [3:0] a, b, input logic e, output logic [3:0] y);
  always_comb begin
    begin
      y = a;
      if (e) y = b;
    end
    if (e) y = a;
  end
endmodule
