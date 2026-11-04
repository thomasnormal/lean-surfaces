/*
:name: assoc_bound_key
:description: §7.8 — literal-initialized associative-array keys lower to finite scalar cells
:tags: 7.8 10.4.1
:type: simulation
*/
module top;
  initial begin
    int by_name[string];
    int by_index[int];
    string name_key = "beta";
    int index_key = 7;

    by_name[name_key] = 15;
    by_index[index_key] = 27;

    if (by_name[name_key] == 15 && by_index[index_key] == 27)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
