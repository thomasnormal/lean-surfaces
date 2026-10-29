/*
:name: pure_diagnostic_markers_adapter
:description: Existing inert diagnostic markers are erased by the adapter.
:tags: 20.4 20.17 21.6 21.7 32.3
:type: simulation
*/
module top;
  initial begin
    $monitoroff;
    $monitoron();
    $dumpfile("trace.vcd");
    $dumpvars(0, top);
    $dumpon;
    $dumpoff;
    $dumpall;
    $dumpflush;
    $dumplimit(1024);
    $dumpportsflush();
    $sdf_annotate("timing.sdf");
    $timeformat(-9, 2, " ns", 10);
    $system();
    $display("PASS");
    $finish;
  end
endmodule
