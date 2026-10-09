module top;
  logic signed [3:0] signed_source;
  logic [3:0] unsigned_source;
  time explicit_bits;
  time explicit_sum;
  time implicit_sum;

  initial begin
    signed_source = 4'b1001;
    unsigned_source = 4'b1001;
    explicit_bits = time'(signed_source);
    explicit_sum = time'(signed_source) + unsigned_source;
    implicit_sum = signed_source + unsigned_source;
    $display("unsigned-type=[%h][%h][%h]", explicit_bits, explicit_sum, implicit_sum);
    if ((explicit_bits === 64'hfffffffffffffff9) &&
        (explicit_sum === 64'h0000000000000002) &&
        (implicit_sum === 64'h0000000000000012) &&
        !(time'(signed_source) < 0))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
