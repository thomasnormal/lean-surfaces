/* A module-scope event declaration is inert on the time-zero self-check path. */
module top;
  event named_ev;
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
