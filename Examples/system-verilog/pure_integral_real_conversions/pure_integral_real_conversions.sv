/*
:name: pure_integral_real_conversions
:description: discarded pure integral operands for real conversions are inert
:tags: 20.5
:type: simulation
*/
module top;
  integer value;
  logic [63:0] real_bits;
  logic [31:0] short_bits;

  initial begin
    value = 3;
    real_bits = 64'h1;
    short_bits = 32'h2;

    $itor(value + 2);
    $bitstoreal(real_bits | 64'h2);
    $bitstoshortreal(short_bits ^ 32'h1);

    $display("PASS");
    $finish;
  end
endmodule
