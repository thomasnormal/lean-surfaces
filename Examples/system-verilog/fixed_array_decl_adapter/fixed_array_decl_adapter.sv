/*
:name: fixed_array_decl_adapter
:description: A fixed unpacked integral array lowers to flat self-check cells.
:tags: 7.4
:type: simulation
*/
module top;
  initial begin
    int values[2];
    values[0] = 10;
    values[1] = 20;
    if (values[0] == 10 && values[1] == 20)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
