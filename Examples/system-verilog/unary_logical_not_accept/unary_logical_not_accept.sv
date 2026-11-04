// Small self-check witness for four-state logical-not.
module top;
  logic [1:0] value;
  logic result;

  initial begin
    value = 2'b00;
    result = !value;
    if (result !== 1'b1) begin
      $display("FAIL logical not zero");
      $finish;
    end

    value = 2'b01;
    result = !value;
    if (result !== 1'b0) begin
      $display("FAIL logical not one");
      $finish;
    end

    value = 2'b0x;
    result = !value;
    if (result !== 1'bx) begin
      $display("FAIL logical not unknown");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
