/*
:name: dist_uniform_variable_bounds
:description: §18.13.3 — source-pure integer bounds feed seeded $dist_uniform
:tags: 18.13.3 20.14.2
:type: simulation
*/
module top;
  initial begin
    integer seed;
    integer value;
    integer low;
    integer high;
    integer pass;
    seed = 42;
    low  = 1;
    high = 10;
    pass = 1;
    for (int i = 0; i < 100; i++) begin
      value = $dist_uniform(seed, low, high);
      if (value < low || value > high) begin
        $display("FAIL $dist_uniform returned %0d outside [%0d,%0d]", value, low, high);
        pass = 0;
      end
    end
    if (pass)
      $display("PASS");
    $finish;
  end
endmodule
