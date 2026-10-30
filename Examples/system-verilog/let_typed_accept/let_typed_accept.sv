// Small self-check witness for typed local let formals.
module top;
  logic [3:0] result;
  let twice(logic [3:0] a) = a + a;

  initial begin
    result = twice(4'd3);
    if (result !== 4'd6) begin
      $display("FAIL typed let");
      $finish;
    end

    result = twice(4'd5);
    if (result !== 4'd10) begin
      $display("FAIL typed let second");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
