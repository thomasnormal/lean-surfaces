// Small self-check witness for unary reduction operators.
module top;
  logic [3:0] value;
  logic result;

  initial begin
    value = 4'b1011;
    if ((|value) !== 1'b1) begin
      $display("FAIL reduction or");
      $finish;
    end
    if ((&value) !== 1'b0) begin
      $display("FAIL reduction and");
      $finish;
    end
    if ((^value) !== 1'b1) begin
      $display("FAIL reduction xor");
      $finish;
    end

    value = 4'b11x1;
    result = &value;
    if (result !== 1'bx) begin
      $display("FAIL reduction unknown");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
