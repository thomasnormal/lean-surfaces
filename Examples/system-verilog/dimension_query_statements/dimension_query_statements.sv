/* Discarded fixed dimension queries have no represented state effect. */
module top;
  logic [7:0] value;
  initial begin
    $size(value);
    $high(value);
    $left(value);
    $right(value);
    $low(value);
    $increment(value);
    $dimensions(value);
    $unpacked_dimensions(value);
    $display("PASS");
    $finish;
  end
endmodule
