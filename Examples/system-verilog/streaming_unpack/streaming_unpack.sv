/*
:name: streaming_unpack
:description: §11.4.14 — right streaming unpack into scalar targets
:tags: 11.4.14
:type: simulation
*/
module top;
  initial begin
    bit [15:0] source;
    bit [7:0] hi, lo;
    source = 16'hABCD;
    {>> {hi, lo}} = source;
    if (hi === 8'hAB && lo === 8'hCD)
      $display("PASS");
    else
      $display("FAIL %h %h", hi, lo);
    $finish;
  end
endmodule
