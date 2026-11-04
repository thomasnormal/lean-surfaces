module top;
  initial begin
    typedef struct packed {
      logic [2:0] first;
      bit second;
      logic [3:0] last;
    } packet_t;
    typedef union packed {logic [7:0] word; bit [7:0] other;} union_t;
    typedef logic [1:0][2:0] packed_array_t;
    if ($bits(packet_t) == 8 && $bits(union_t) == 8 &&
        $bits(packed_array_t) == 6)
      $display("PASS");
    else
      $display("FAIL: packed aggregate type widths");
    $finish;
  end
endmodule
// REFERENCE: 4e6d1923629f7be2424b3e02 xrun(64) 24.03-s004 2026-10-10T03:16:26Z; PASS.
