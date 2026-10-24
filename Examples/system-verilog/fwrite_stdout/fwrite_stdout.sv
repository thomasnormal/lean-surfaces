/* The predefined stdout descriptor preserves fwrite's no-newline behavior. */
module top;
  initial begin
    $fwrite(32'h8000_0001, "PASS");
    $display("");
    $finish;
  end
endmodule
