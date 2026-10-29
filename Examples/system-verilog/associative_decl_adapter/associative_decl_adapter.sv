/*
:name: associative_decl_adapter
:description: Static associative-array declarations are erased metadata in the adapter.
:tags: 7.8
:type: simulation
*/
module top;
  initial begin
    int score[string];
    $display("PASS");
    $finish;
  end
endmodule
