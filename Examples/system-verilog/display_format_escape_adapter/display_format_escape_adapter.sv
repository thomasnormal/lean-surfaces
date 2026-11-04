/* Display format escapes are consumed by the represented call itself. */
// Expected transcript includes: octal S, PASS.
module top;
  initial begin
    $display("octal \123");
    $display("PASS");
    $finish;
  end
endmodule
