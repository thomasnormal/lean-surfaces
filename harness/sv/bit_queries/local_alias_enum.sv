module top;
  initial begin
    typedef int unsigned count_t;
    typedef enum logic [4:0] {LOW = 5'd3, HIGH = 5'd4} state_t;
    if ($bits(count_t) == 32 && $bits(state_t) == 5 &&
        $bits(LOW) == 5 && $bits(HIGH) == 5)
      $display("PASS");
    else
      $display("FAIL: local alias and enum widths");
    $finish;
  end
endmodule
// REFERENCE: 81569dd2a96973564ed4cc4b xrun(64) 24.03-s004 2026-10-10T03:16:23Z; PASS.
