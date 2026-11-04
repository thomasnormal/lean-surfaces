/* A literal-only string concatenation has no represented self-check state. */
module top;
  string value;
  initial begin
    value = {"left", "-", "right"};
    $display("PASS");
    $finish;
  end
endmodule
