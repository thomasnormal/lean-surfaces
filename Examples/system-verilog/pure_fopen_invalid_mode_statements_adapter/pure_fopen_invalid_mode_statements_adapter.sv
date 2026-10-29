/*
:name: pure_fopen_invalid_mode_statements_adapter
:description: A discarded fopen call with an invalid literal mode has no adapter state.
:tags: 21.6
:type: simulation
*/
module top;
  initial begin
    $fopen("/tmp/lean_surfaces_invalid_mode_statement", "z");
    $display("PASS");
    $finish;
  end
endmodule
