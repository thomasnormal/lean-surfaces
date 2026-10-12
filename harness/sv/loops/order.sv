module top;
  integer index, mirror, total, initializer;
  initial begin
    initializer = 0;
    total = 0;
    for (index = 0, initializer = initializer + 1, mirror = index;
         index < 4; index++, mirror = index)
      total = total + mirror;
    if (total !== 6 || index !== 4 || mirror !== 4 || initializer !== 1)
      $display("FAIL ordered header");
    total = 0;
    for (int local_index = 0; local_index < 3; local_index += 1)
      total = total + local_index;
    if (total !== 3) $display("FAIL local initializer");
    for (index = 4; index > 0; --index) total += index;
    if (total !== 13) $display("FAIL decrement");
    for (;;) break;
    $display("PASS");
    $finish;
  end
// REFERENCE: 920a7a14d18b2d3327f7912c independent-simulator 2026-10-12T11:57:36Z
endmodule
