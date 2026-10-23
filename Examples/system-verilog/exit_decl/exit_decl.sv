/*
:name: exit_decl
:description: IEEE 1800-2023 Section 24.7 -- $exit from a module-originating
  initial process is ignored, so execution continues normally.
:tags: 24.7
:type: simulation
*/
module top;
  initial begin
    $exit;
    $display("PASS");
    $finish;
  end
endmodule
