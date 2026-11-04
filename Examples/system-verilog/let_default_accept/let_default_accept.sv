// Small self-check witness for let defaults and named actual binding.
module top;
  int result;
  let add(a, b = 2) = a + b;

  initial begin
    result = add(3);
    if (result !== 5) begin
      $display("FAIL let default");
      $finish;
    end

    result = add(.b(4), .a(3));
    if (result !== 7) begin
      $display("FAIL let named");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
