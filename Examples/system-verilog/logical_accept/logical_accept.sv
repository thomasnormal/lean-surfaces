// Small self-check witness for logical conjunction and disjunction.
module top;
  logic left;
  logic right;
  logic result;

  initial begin
    left = 1'b1;
    right = 1'b1;
    result = left && right;
    if (result !== 1'b1) begin
      $display("FAIL logical and");
      $finish;
    end

    right = 1'b0;
    result = left || right;
    if (result !== 1'b1) begin
      $display("FAIL logical or");
      $finish;
    end

    left = 1'b0;
    result = left && right;
    if (result !== 1'b0) begin
      $display("FAIL logical false");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
