/*
:name: array_named_display
:description: A one-dimensional fixed array can be rendered by a `%p` diagnostic after a pure pattern assignment.
:tags: 5.11 10.9.1 diagnostic
:type: simulation
// ARRAY '{1, 2, 3}
// PASS
*/
module top;
  typedef int triple[1:3];
  initial begin
    triple t;
    t = '{1, 2, 3};
    $display("ARRAY %p", t);
    if (t[1] == 1 && t[2] == 2 && t[3] == 3)
      $display("PASS");
    else
      $display("FAIL: t=%p", t);
    $finish;
  end
endmodule
