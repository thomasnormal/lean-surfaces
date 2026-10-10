module top;
  initial begin
    logic [5:0] value;
    logic [2:0] control;
    integer selected;
    value = 6'b10xz01;
    control = 3'b101;
    selected = $countbits(value, control, control);
    if (selected != 2 || $countbits(value, 3'b110) != 2 ||
        $countbits(value, -1) != 2 || $countbits(value, 3'b10x) != 1 ||
        $countbits(value, 3'b01z) != 1) begin
      $display("FAIL: control truncation or deduplication");
      $finish;
    end
    control = 3'b01x;
    if ($countbits(value, control, 1'bz) != 2) begin
      $display("FAIL: live unknown control");
      $finish;
    end
    value = 6'b111111;
    control = 3'b001;
    if ($countbits(value, control) == 6 && $countones(value) == 6)
      $display("PASS");
    else
      $display("FAIL: query did not read current values");
    $finish;
  end
endmodule
// REFERENCE: 108fb59cb5314df733145d10 xrun(64) 24.03-s004 2026-10-10T09:45:14Z; PASS.
