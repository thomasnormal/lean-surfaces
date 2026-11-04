/*
:name: unpacked_concat_initializer
:description: IEEE 1800-2023 Section 10.10.1 -- unpacked array concatenation initializers mix arrays and elements.
:tags: 10.10.1
:type: simulation
*/
module top;
  typedef int triple_t [0:2];
  typedef int nine_t [0:8];

  initial begin
    triple_t prefix = '{1, 2, 3};
    nine_t values = {prefix, 4, triple_t'{5, 6, 7}, 8, 9};

    if (values[0] == 1 && values[3] == 4 &&
        values[4] == 5 && values[8] == 9)
      $display("PASS");
    else
      $display("FAIL: values=%0d,%0d,%0d,%0d",
               values[0], values[3], values[4], values[8]);
    $finish;
  end
endmodule
