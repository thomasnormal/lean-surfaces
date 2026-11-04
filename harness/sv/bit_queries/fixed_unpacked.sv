module top;
  initial begin
    typedef logic [2:0] array_t [4:1][0:2];
    typedef struct {logic [2:0] first; bit [4:0] second;} record_t;
    typedef record_t records_t [0:2];
    if ($bits(array_t) == 36 && $bits(record_t) == 8 &&
        $bits(records_t) == 24)
      $display("PASS");
    else
      $display("FAIL: fixed unpacked type widths");
    $finish;
  end
endmodule
// REFERENCE: 9431de080b30f0a241bc444f xrun(64) 24.03-s004 2026-10-10T03:16:20Z; PASS.
