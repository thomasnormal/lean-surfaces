/*
:name: dynamic_array_resize_fixed_source
:description: IEEE 1800-2023 Section 7.5.1 -- a finite scalar dynamic-array
  resize copies a distinct fixed-array source in declared order and pads new
  elements by default.
:tags: 7.5.1
:type: simulation
*/
module top;
  initial begin
    int fixed_source[3] = '{8, 9, 10};
    int dynamic_result[];
    dynamic_result = new[4](fixed_source);
    if (dynamic_result[0] == 8 && dynamic_result[1] == 9 &&
        dynamic_result[2] == 10 && dynamic_result[3] == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
