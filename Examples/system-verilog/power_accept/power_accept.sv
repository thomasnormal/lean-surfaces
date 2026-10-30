// Small self-check witness for four-state integral power.
module top;
  logic [7:0] base;
  logic [3:0] exponent;

  initial begin
    base = 8'd3;
    exponent = 4'd5;
    if ((base ** exponent) !== 8'd243) begin
      $display("FAIL positive");
      $finish;
    end

    exponent = 4'd0;
    if ((base ** exponent) !== 8'd1) begin
      $display("FAIL zero exponent");
      $finish;
    end

    base = 8'bx0000001;
    if ((base ** exponent) !== 8'bxxxxxxxx) begin
      $display("FAIL unknown base");
      $finish;
    end

    base = 8'd1;
    exponent = 4'bz001;
    if ((base ** exponent) !== 8'bxxxxxxxx) begin
      $display("FAIL unknown exponent");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
