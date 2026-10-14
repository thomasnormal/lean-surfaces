module clog2;
  logic [31:0] zero;
  logic [31:0] one;
  logic [31:0] eight;
  logic [31:0] nine;
  logic [31:0] negative;

  initial begin
    zero = $clog2(0);
    one = $clog2(1);
    eight = $clog2(8);
    nine = $clog2(9);
    negative = $clog2(-1);
    if (zero == 0 && one == 0 && eight == 3 && nine == 4 && negative == 32)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
