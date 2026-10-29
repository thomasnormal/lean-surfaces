/*
:name: pure_type_width_query_statements_adapter
:description: Discarded type and width queries do not evaluate their arguments.
:tags: 20.6
:type: simulation
*/
module top;
  int counter;
  initial begin
    $typename(counter++);
    $bits(counter++);
    if (counter == 0)
      $display("PASS");
    else
      $display("FAIL: discarded type/width query evaluated its argument");
    $finish;
  end
endmodule
