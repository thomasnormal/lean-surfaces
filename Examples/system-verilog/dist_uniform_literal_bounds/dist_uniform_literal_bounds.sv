/*
:name: dist_uniform_literal_bounds
:description: §20.14.2 — literal nonnegative start/end bounds constrain a seeded $dist_uniform result
:tags: 20.14.2
:type: simulation
*/
module top;
  initial begin
    integer seed;
    integer value;
    seed = 42;
    value = $dist_uniform(seed, 10, 20);
    if (value >= 10 && value <= 20)
      $display("PASS");
    else
      $display("FAIL");
  end
endmodule
