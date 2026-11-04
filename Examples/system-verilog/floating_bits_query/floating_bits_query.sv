/*
:name: floating_bits_query
:description: $bits on real and shortreal type expressions reads fixed metadata
:tags: 6.24.3
:type: simulation
*/
module top;
  initial begin
    if ($bits(real) === 64 && $bits(shortreal) === 32)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
