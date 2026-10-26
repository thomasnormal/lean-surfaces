/* A discarded atoreal conversion of a literal string has no modeled state. */
module top;
  string text;
  initial begin
    text = "1.5";
    text.atoreal();
    $display("PASS");
    $finish;
  end
endmodule
