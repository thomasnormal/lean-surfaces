/* A pure static initializer may read an earlier static declaration. */
module top;
  initial begin
    logic [3:0] value = 4'b10xz;
    logic [3:0] result = value << 0;
    if (result === value)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
