// IEEE 1800-2023 6.19: signed/unsigned members and generated enum names.
module top;
  typedef enum byte {NEGATIVE = -2, FOLLOWING, POSITIVE = 3} signed_t;
  typedef enum int unsigned {HIGH = 32'h80000000, HIGH_NEXT} unsigned_t;
  typedef enum bit [3:0] {MODE[3] = 4, LAST} ranged_t;
  signed_t signed_value;
  unsigned_t unsigned_value;
  ranged_t ranged_value;
  initial begin
    signed_value = NEGATIVE;
    unsigned_value = HIGH_NEXT;
    ranged_value = MODE2;
    if (signed_value == -2 && FOLLOWING == -1 && POSITIVE == 3 &&
        unsigned_value == 32'h80000001 && HIGH > 0 &&
        MODE0 == 4 && MODE1 == 5 && ranged_value == 6 && LAST == 7)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: a3b44c307e3e85567e673156 xrun(64) 24.03-s004 2026-10-09T23:17:09Z; PASS.
