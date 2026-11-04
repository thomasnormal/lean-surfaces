/*
:name: assoc_next_prev_history
:description: IEEE 1800-2023 §7.9.4-7.9.5 finite associative-array next and prev
:tags: 7.9.4 7.9.5 associative array endpoint
:type: simulation
*/
module top;
  int values[int];
  int key;
  int result;
  initial begin
    values[1] = 10;
    values[3] = 30;
    values[5] = 50;
    key = 1;
    result = values.next(key);
    if (result == 1 && key == 3) $display("PASS1");
    result = values.next(key);
    if (result == 1 && key == 5) $display("PASS2");
    result = values.prev(key);
    if (result == 1 && key == 3) $display("PASS3");
    values.prev(key);
    if (key == 1) $display("PASS4");
    result = values.prev(key);
    if (result == 0 && key == 1) $display("PASS5");
  end
endmodule
