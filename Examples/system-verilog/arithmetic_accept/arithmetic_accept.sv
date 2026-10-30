// Small self-check witness for four-state integral arithmetic operators.
module top;
  logic [7:0] left;
  logic [7:0] right;
  logic [7:0] result;

  initial begin
    left = 8'd12;
    right = 8'd5;

    if ((left + right) !== 8'd17) begin
      $display("FAIL addition");
      $finish;
    end
    if ((left - right) !== 8'd7) begin
      $display("FAIL subtraction");
      $finish;
    end
    if ((left * right) !== 8'd60) begin
      $display("FAIL multiplication");
      $finish;
    end
    if ((left / right) !== 8'd2) begin
      $display("FAIL division");
      $finish;
    end
    if ((left % right) !== 8'd2) begin
      $display("FAIL remainder");
      $finish;
    end

    left = 8'b1x01;
    result = left + right;
    if (result !== 8'bxxxxxxxx) begin
      $display("FAIL addition unknown");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
