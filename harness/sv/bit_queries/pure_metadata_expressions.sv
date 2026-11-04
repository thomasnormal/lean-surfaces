module top;
  initial begin
    typedef bit large_sign_t [65536][32768];
    typedef bit large_wrap_t [65536][65536];
    logic [7:0] subject;
    integer index;
    subject = 8'b10xz0011;
    index = 2;
    if ($bits(16'd1) != 16 || $bits(subject) != 8 ||
        $bits(subject[index]) != 1 || $bits(subject[index +: 3]) != 3 ||
        $bits(subject << index) != 8 || $bits(~subject) != 8 ||
        $bits(&subject) != 1 || $bits({subject, 2'bxz}) != 10 ||
        $bits(subject + 16'd1) != 16 || $bits(subject == 8'd0) != 1 ||
        $bits(1'b0 ? subject : 16'd0) != 16 ||
        $bits(large_sign_t) !== 32'sh8000_0000 ||
        $bits(large_sign_t) >= 0 || $bits(large_wrap_t) !== 32'sd0) begin
      $display("FAIL: pure expression metadata widths");
      $finish;
    end
    if (subject === 8'b10xz0011 && index == 2)
      $display("PASS");
    else
      $display("FAIL: pure metadata query changed state");
    $finish;
  end
endmodule
// REFERENCE: 16daebfd761672d937b08a0e xrun(64) 24.03-s004 2026-10-10T03:25:14Z; PASS.
