/*
:name: pure_associative_endpoint_delete_statements_adapter
:description: Finite associative endpoint statements and literal deletes are replayed in the adapter.
:tags: 7.9.2 7.9.4 7.9.5
:type: simulation
*/
module top;
  int values[int];
  int key;
  initial begin
    values[2] = 20;
    values[5] = 50;
    values.last(key);
    if (key == 5)
      $display("PASS");
    else
      $display("FAIL1");
    values.delete(5);
    values.first(key);
    if (key == 2)
      $display("PASS2");
    else
      $display("FAIL2");
    values.delete();
    key = 99;
    values.first(key);
    if (key == 99)
      $display("PASS3");
    else
      $display("FAIL3");
    $finish;
  end
endmodule
