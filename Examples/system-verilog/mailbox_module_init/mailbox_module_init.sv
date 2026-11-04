/* A module-scope unbounded mailbox initializer is declaration metadata. */
/*
:name: mailbox_module_init
:description: IEEE 1800-2023 Section 15.4.1 -- an unbounded mailbox initialized with new() may be used by later literal FIFO operations.
:tags: 15.4.1 15.4.6 mailbox module initializer
:type: simulation
*/
module top;
  mailbox mbx = new();
  int value;
  int result;

  initial begin
    mbx.put(7);
    result = mbx.try_get(value);
    if (result > 0 && value == 7)
      $display("PASS");
    else
      $display("FAIL: result=%0d value=%0d", result, value);
    $finish;
  end
endmodule
