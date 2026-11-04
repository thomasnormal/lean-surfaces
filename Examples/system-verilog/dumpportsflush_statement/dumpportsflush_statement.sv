/* A port-dump flush changes only an external waveform stream. */
module top;
  initial begin
    $dumpportsflush();
    $display("PASS");
    $finish;
  end
endmodule
