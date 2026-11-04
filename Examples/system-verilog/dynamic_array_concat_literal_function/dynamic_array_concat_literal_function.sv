/*
:name: dynamic_array_concat_literal_function
:description: IEEE 1800-2023 Section 7.5 -- a literal-return function
  contributes one scalar cell to an unpacked dynamic-array concatenation.
:tags: 7.5 13.4
:type: simulation
*/
module top;
  function automatic int get_value();
    get_value = 20;
  endfunction

  initial begin
    int values[];
    values = {10, get_value(), 30};
    if (values.size() == 3 && values[0] == 10 && values[1] == 20 &&
        values[2] == 30)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
