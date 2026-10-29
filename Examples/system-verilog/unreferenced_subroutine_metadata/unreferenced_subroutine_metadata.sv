/* An uncalled subroutine is declaration metadata in the legacy tier. */
module top;
  task unused;
    $display("NEVER");
  endtask

  initial begin
    $display("PASS");
    $finish;
  end
endmodule
