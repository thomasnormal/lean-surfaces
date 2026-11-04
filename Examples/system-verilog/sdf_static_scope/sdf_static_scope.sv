/*
:name: sdf_static_scope
:description: §32.2–32.3 — literal SDF annotation with a static module scope is inert in the time-zero self-check surface
:tags: 32.2 32.3
:type: simulation
*/
module top;
  initial begin
    $sdf_annotate("/tmp/no-such-sdf.sdf", top);
    $display("PASS");
    $finish;
  end
endmodule
