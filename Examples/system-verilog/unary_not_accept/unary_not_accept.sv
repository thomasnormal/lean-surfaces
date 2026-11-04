// Small self-check witness for four-state unary bitwise-not.
module top;
  logic [3:0] value;
  logic [3:0] result;

  initial begin
    value = 4'b1010;
    result = ~value;
    if (result !== 4'b0101) begin
      $display("FAIL unary not known");
      $finish;
    end

    value = 4'b10xz;
    result = ~value;
    if (result !== 4'b01xx) begin
      $display("FAIL unary not unknown");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
