/* Fixed-width real conversion results remain metadata-only for $bits. */
module top;
  initial begin
    shortreal sr = 1.0;
    real dr = 1.0;
    if ($bits($shortrealtobits(sr)) === 32 &&
        $bits($realtobits(dr)) === 64)
      $display("PASS");
    else
      $display("FAIL: unexpected conversion width");
    $finish;
  end
endmodule
