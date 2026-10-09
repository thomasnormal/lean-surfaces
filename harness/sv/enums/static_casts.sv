// IEEE 1800-2023 6.19 and 6.24: static casts do not check membership.
module top;
  typedef enum logic signed [7:0] {WIDE_ZERO = 0} wide_t;
  typedef enum bit [2:0] {NARROW_ZERO = 0} narrow_t;
  logic signed [3:0] signed_source = 4'b1110;
  logic [3:0] unsigned_source = 4'b1110;
  wide_t wide;
  narrow_t narrow;
  initial begin
    wide = wide_t'(signed_source);
    if (wide === 8'b11111110) begin
      wide = wide_t'(unsigned_source);
      narrow = narrow_t'(11);
      if (wide === 8'b00001110 && narrow === 3'b011 && wide_t'(99) == 99)
        $display("PASS");
      else
        $display("FAIL");
    end else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 597a07af17820fb0ebdea85d xrun(64) 24.03-s004 2026-10-09T23:17:03Z; PASS.
