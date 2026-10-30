// Small self-check witness for scalar conditional expressions.
module top;
  logic value;
  logic [1:0] result;

  initial begin
    value = 1'b1;
    result = value ? 2'd1 : 2'd2;
    if (result !== 2'd1) begin
      $display("FAIL conditional true");
      $finish;
    end

    value = 1'b0;
    result = value ? 2'd1 : 2'd2;
    if (result !== 2'd2) begin
      $display("FAIL conditional false");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
