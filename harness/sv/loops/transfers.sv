module top;
  integer index, total, steps, count;
  initial begin
    total = 0;
    steps = 0;
    for (index = 0; index < 5; index += 1, steps += 1) begin
      if (index == 1) continue;
      if (index == 4) break;
      total += index;
    end
    if (total !== 5 || steps !== 4 || index !== 4)
      $display("FAIL for transfers");
    total = 0;
    count = 4;
    repeat (count) begin
      total += 1;
      count = 0;
      continue;
      total += 100;
    end
    if (total !== 4) $display("FAIL repeat continue");
    total = 0;
    for (index = 0; index < 3; index += 1) begin
      repeat (5) begin
        total += 1;
        break;
      end
      total += 10;
    end
    if (total !== 33 || index !== 3) $display("FAIL nested break");
    $display("PASS");
    $finish;
  end
// REFERENCE: 16ad5e7c59d0b1d525f33f83 independent-simulator 2026-10-12T11:57:39Z
endmodule
