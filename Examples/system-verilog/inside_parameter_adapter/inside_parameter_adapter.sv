/* Bounded inside items use the same elaborated parameter literals as M0. */
// Expected transcript includes: 0, PASS.
module top;
  int result;
  int value = 12;
  localparam int LOW = 5;
  localparam int HIGH = 7;

  initial begin
    result = value inside {LOW, HIGH};
    $display("%0d", result);
    $display("PASS");
    $finish;
  end
endmodule
