// Small self-check witness for four-state unary-minus arithmetic.
module top;
  logic [3:0] value;
  logic signed [7:0] result;

  initial begin
    value = 4'd3;
    result = -value;
    if (result !== -8'sd3) begin
      $display("FAIL unary minus known");
      $finish;
    end

    value = 4'b1x01;
    result = -value;
    if (result !== 8'bxxxxxxxx) begin
      $display("FAIL unary minus unknown");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
