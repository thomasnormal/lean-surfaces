/*
:name: unpacked_struct_nested_pattern
:description: IEEE 1800-2023 10.9.2 — nested struct assignment patterns flatten recursively
:tags: 10.9.2
:type: simulation
*/
module top;
  typedef struct { int a; struct { int b; int c; } inner; } payload_t;
  payload_t value;
  initial begin
    value = '{a: 1, inner: '{b: 2, c: 3}};
    if (value.a == 1 && value.inner.b == 2 && value.inner.c == 3)
      $display("PASS1");
    else
      $display("FAIL1");
    value = '{default: 7};
    if (value.a == 7 && value.inner.b == 7 && value.inner.c == 7)
      $display("PASS2");
    else
      $display("FAIL2");
    $finish;
  end
endmodule
