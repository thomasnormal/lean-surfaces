// Small self-check witness for four-state binary bitwise operators.
module top;
  logic [3:0] left;
  logic [3:0] right;
  logic [3:0] result;

  initial begin
    left = 4'b1010;
    right = 4'b1100;

    if ((left & right) !== 4'b1000) begin
      $display("FAIL bitwise and");
      $finish;
    end
    if ((left | right) !== 4'b1110) begin
      $display("FAIL bitwise or");
      $finish;
    end
    if ((left ^ right) !== 4'b0110) begin
      $display("FAIL bitwise xor");
      $finish;
    end

    left = 4'b10x1;
    right = 4'b1111;
    result = left & right;
    if (result !== 4'b10x1) begin
      $display("FAIL bitwise and unknown");
      $finish;
    end
    result = left | right;
    if (result !== 4'b1111) begin
      $display("FAIL bitwise or unknown");
      $finish;
    end
    result = left ^ right;
    if (result !== 4'b01x0) begin
      $display("FAIL bitwise xor unknown");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
