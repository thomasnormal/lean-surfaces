/*
:name: dist_uniform_scalar_seeded
:description: §20.14.2 — a direct bounded $dist_uniform assignment updates its inout seed and is repeatable from equal seeds
:tags: 20.14.2
:type: simulation
*/
module top;
  initial begin
    integer seed_a, seed_b;
    integer a, b;
    seed_a = 9001;
    seed_b = 9001;
    a = $dist_uniform(seed_a, 0, 1000);
    b = $dist_uniform(seed_b, 0, 1000);
    if (a == b && seed_a == seed_b && seed_a != 9001)
      $display("PASS");
    else
      $display("FAIL");
  end
endmodule
