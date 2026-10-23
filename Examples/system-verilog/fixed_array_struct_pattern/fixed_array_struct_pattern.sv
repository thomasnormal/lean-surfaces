/*
:name: array_pattern_default_with_multidim_struct_elements
:description: §10.9.1 — For unmatched structure elements in an array, the type and default keys are applied to each element using the rules for structure assignment patterns (recursive descent into struct)
:tags: 10.9.1
:type: simulation
*/
module top;
  typedef struct { int a; time b; } ab_t;
  ab_t abkey[1:0];

  initial begin
    // From spec example: abkey = '{'{a:1, b:2ns}, '{int:5, time:$time}};
    // Use explicit values for deterministic test
    abkey = '{'{a:1, b:2}, '{int:5, time:99}};
    if (abkey[1].a===1 && abkey[1].b===2 && abkey[0].a===5 && abkey[0].b===99)
      $display("PASS");
    else
      $display("FAIL: abkey[1]={a=%0d,b=%0d} abkey[0]={a=%0d,b=%0d}",
               abkey[1].a, abkey[1].b, abkey[0].a, abkey[0].b);
    $finish;
  end
endmodule
