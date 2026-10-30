// Small self-check witness for four-state equality and relational operators.
module top;
  logic [3:0] left;
  logic [3:0] right;
  logic result;

  initial begin
    left = 4'd3;
    right = 4'd4;

    if ((left == right) !== 1'b0) begin
      $display("FAIL equality");
      $finish;
    end
    if ((left != right) !== 1'b1) begin
      $display("FAIL inequality");
      $finish;
    end
    if ((left < right) !== 1'b1) begin
      $display("FAIL less-than");
      $finish;
    end
    if ((left <= right) !== 1'b1) begin
      $display("FAIL less-equal");
      $finish;
    end
    if ((left > right) !== 1'b0) begin
      $display("FAIL greater-than");
      $finish;
    end
    if ((left >= right) !== 1'b0) begin
      $display("FAIL greater-equal");
      $finish;
    end

    left = 4'b1x01;
    right = 4'b1001;
    result = left == right;
    if (result !== 1'bx) begin
      $display("FAIL equality unknown");
      $finish;
    end
    result = left < right;
    if (result !== 1'bx) begin
      $display("FAIL less-than unknown");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
