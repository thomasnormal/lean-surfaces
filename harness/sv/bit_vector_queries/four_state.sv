module top;
  initial begin
    logic [5:0] mixed;
    mixed = 6'b10xz01;
    if ($countbits(mixed, 1'b0) == 2 && $countbits(mixed, 1'b1) == 2 &&
        $countbits(mixed, 1'bx) == 1 && $countbits(mixed, 1'bz) == 1 &&
        $countbits(mixed, 1'b0, 1'b1, 1'bx, 1'bz) == 6 &&
        $countbits(mixed, 1'b1, 1'bx, 1'b1, 1'bx) == 3 &&
        $countones(mixed) == 2 && $isunknown(mixed) &&
        !$onehot(mixed) && !$onehot0(mixed) &&
        $onehot(4'bx001) && $onehot0(4'bz000) &&
        !$onehot(4'bxxxx) && $onehot0(4'bxxxx) &&
        !$isunknown(4'b0110) && $isunknown(4'bzzzz))
      $display("PASS");
    else
      $display("FAIL: four-state bit-vector queries");
    $finish;
  end
endmodule
// REFERENCE: a981cb091d8f80418fb934e3 xrun(64) 24.03-s004 2026-10-10T09:44:17Z; PASS.
