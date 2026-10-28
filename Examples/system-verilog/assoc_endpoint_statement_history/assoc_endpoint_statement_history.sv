/*
:name: assoc_endpoint_statement_history
:description: IEEE 1800-2023 §7.9.4-7.9.5 discarded finite associative endpoints
:tags: 7.9.4 7.9.5 associative array endpoint statement
:type: simulation
*/
module top;
  int values[int];
  int key;
  initial begin
    values[4] = 40;
    values[9] = 90;
    values.last(key);
    if (key == 9)
      $display("PASS");
    else
      $display("FAIL1");
    values.delete(9);
    values.first(key);
    if (key == 4)
      $display("PASS2");
    else
      $display("FAIL2");
    values.delete();
    key = 17;
    values.first(key);
    if (key == 17)
      $display("PASS3");
    else
      $display("FAIL3");
    $finish;
  end
endmodule
