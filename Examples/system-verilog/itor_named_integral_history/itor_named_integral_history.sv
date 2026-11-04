/* A source-pure named integral can feed exact $itor conversions. */
module top;
  integer value;
  logic [63:0] real_bits;
  logic [31:0] short_bits;
  initial begin
    value = -17;
    real_bits = $realtobits($itor(value));
    short_bits = $shortrealtobits($itor(value));
    if ($rtoi($itor(value)) === -17
        && real_bits === 64'hc031_0000_0000_0000
        && short_bits === 32'hc188_0000)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
