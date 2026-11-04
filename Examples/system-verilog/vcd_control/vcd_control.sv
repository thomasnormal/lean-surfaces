/*
:name: vcd_control
:description: IEEE 1800-2023 Sections 21.6-21.7 -- VCD control calls affect
  only external waveform recording and leave the self-check output unchanged.
:tags: 21.6 21.7
:type: simulation
*/
module top;
  initial begin
    $dumpon;
    $dumpoff;
    $dumpall;
    $dumpflush;
    $dumplimit(1024);
    $display("PASS");
    $finish;
  end
endmodule
