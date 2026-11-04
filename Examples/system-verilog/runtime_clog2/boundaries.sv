module top;
  logic [15:0] value;
  initial begin
    for (int i = 0; i <= 17; i++) begin
      value = i;
      $write("%0d:%0d ", value, $clog2(value));
    end
    $display("");
    value = 255; $write("neighbors %0d ", $clog2(value));
    value = 256; $write("%0d ", $clog2(value));
    value = 257; $display("%0d", $clog2(value));
    $finish;
  end
endmodule
