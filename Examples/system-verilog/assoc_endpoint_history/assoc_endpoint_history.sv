/*
:name: assoc_endpoint_history
:description: IEEE 1800-2023 §7.9.4-7.9.5 finite associative-array first and last
:tags: 7.9.4 7.9.5 associative array endpoint
:type: simulation
*/
module top;
  int values[int];
  int key;
  int result;
  initial begin
    values[3] = 30;
    values[-2] = 20;
    values[7] = 70;
    result = values.first(key);
    if (result == 1 && key == -2)
      $display("PASS");
    else
      $display("FAIL1");
    values.last(key);
    if (key == 7)
      $display("PASS5");
    else
      $display("FAIL5");

    values.delete(-2);
    result = values.first(key);
    if (result == 1 && key == 3)
      $display("PASS2");
    else
      $display("FAIL2");
    result = values.last(key);
    if (result == 1 && key == 7)
      $display("PASS3");
    else
      $display("FAIL3");

    values.delete();
    key = 99;
    result = values.first(key);
    if (result == 0 && key == 99)
      $display("PASS4");
    else
      $display("FAIL4");
    $finish;
  end
endmodule
