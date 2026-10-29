/*
:name: pure_string_atoreal_statements_adapter
:description: A discarded atoreal conversion of a source-pure string has no adapter state.
:tags: 6.16 6.24
:type: simulation
*/
module top;
  string text;
  initial begin
    text = "1.5";
    text.atoreal();
    $display("PASS");
    $finish;
  end
endmodule
