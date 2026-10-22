/*
:name: string_literal_decl
:description: declaration-only string variables may carry unused literal initializers
:tags: 6.16
:type: simulation
*/
module top;
  string module_s = "module";
  initial begin
    string local_s = "local";
    $display("PASS");
    $finish;
  end
endmodule
