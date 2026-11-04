/* A source-pure ASCII string conversion written to opaque real storage. */
module top;
  string text;
  real value;
  initial begin
    text = "3.14";
    value = text.atoreal();
    $display("PASS");
    $finish;
  end
endmodule
