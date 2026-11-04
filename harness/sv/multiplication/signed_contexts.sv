module top;
  logic signed [3:0] negative, positive;
  logic [3:0] unsigned_value;
  logic signed [7:0] signed_product;
  logic [7:0] mixed_product;
  logic [3:0] narrow;

  initial begin
    negative = -4'sd7;
    positive = 4'sd3;
    unsigned_value = 4'd3;
    signed_product = negative * positive;
    mixed_product = negative * unsigned_value;
    narrow = negative * positive;
    if ((signed_product === 8'heb) && (mixed_product === 8'h1b) &&
        (narrow === 4'hb))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 190fe01d70fb2cceb891c261 independent-simulator 2026-10-11T18:11:36Z
