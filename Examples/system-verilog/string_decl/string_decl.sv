/* String declarations are inert on the time-zero self-check path. */
module top;
  string module_s;
  initial begin
    string local_s;
    $display("PASS");
    $finish;
  end
endmodule
