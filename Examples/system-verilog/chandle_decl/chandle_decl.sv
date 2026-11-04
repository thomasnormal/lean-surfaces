/* Chandle declarations are inert metadata on the time-zero self-check path. */
module top;
  chandle module_h;
  initial begin
    chandle local_h;
    $display("PASS");
    $finish;
  end
endmodule
