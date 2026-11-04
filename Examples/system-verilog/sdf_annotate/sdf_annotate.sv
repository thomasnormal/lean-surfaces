/*
:name: sdf_annotate
:description: IEEE 1800-2023 Section 32.3 -- inert filename forms
:tags: 32.3
:type: simulation
*/
module top;
  integer _done = 0;
  initial begin
    $sdf_annotate("timing.sdf");
    $sdf_annotate("noexist.sdf", top, "");
    _done = 1;
    if (!_done) begin $display("FAIL"); $finish; end
    $display("PASS");
    $finish;
  end
endmodule
