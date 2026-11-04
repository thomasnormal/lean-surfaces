/*
:name: dist_uniform_signed_bounds
:description: §20.14.2 — signed literal start/end bounds constrain seeded $dist_uniform results
:tags: 20.14 20.14.2
:type: simulation
*/
module top;
  initial begin
    integer seed_a, seed_b;
    integer negative, crossing;
    seed_a = 42;
    seed_b = 42;
    negative = $dist_uniform(seed_a, -50, -1);
    crossing = $dist_uniform(seed_b, -50, 50);
    if (negative >= -50 && negative <= -1 &&
        crossing >= -50 && crossing <= 50 && seed_a != 42 && seed_b != 42)
      $display("PASS");
    else
      $display("FAIL");
  end
endmodule
