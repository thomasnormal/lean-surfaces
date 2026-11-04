/*
:name: dist_uniform_same_seed_same_sequence
:description: §20.14.2 — $dist_uniform is repeatable: two runs starting from the same seed produce identical sequences of values (audit ref §18.13.3)
:tags: 20.14.2 18.13.3
:type: simulation
*/
module top;
  initial begin
    integer seed_a, seed_b;
    integer a[4], b[4];
    int ok;
    int i;
    ok = 1;

    seed_a = 9001;
    seed_b = 9001;  // identical starting seed

    for (i = 0; i < 4; i++) a[i] = $dist_uniform(seed_a, 0, 1000);
    for (i = 0; i < 4; i++) b[i] = $dist_uniform(seed_b, 0, 1000);

    for (i = 0; i < 4; i++)
      if (a[i] != b[i]) ok = 0;

    if (ok) $display("PASS");
    else $display("FAIL: a={%0d,%0d,%0d,%0d} b={%0d,%0d,%0d,%0d}",
                  a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]);
    $finish;
  end
endmodule
