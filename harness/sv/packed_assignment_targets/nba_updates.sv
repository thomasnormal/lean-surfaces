module top;
  logic [3:0] value;
  logic [1:0] index;
  initial begin
    value = 4'b0000;
    index = 1;
    value[index] <= 1'b1;
    index = 3;
    value[index] <= 1'b1;
    if (value !== 4'b0000) begin
      $display("FAIL: nonblocking selected writes are visible before commit");
      $finish;
    end
    $display("PASS");
    $finish;
  end
endmodule
