/*
:name: pure_real_conversion_statements_adapter
:description: Discarded pure real conversions carry no adapter state.
:tags: 20.5
:type: simulation
*/
module top;
  initial begin
    $itor(-17);
    $bitstoreal(64'h3ff8_0000_0000_0000);
    $bitstoshortreal(32'h3fc0_0000);
    $rtoi(0.5);
    $realtobits(1.0);
    $shortrealtobits(1.0);
    $display("PASS");
    $finish;
  end
endmodule
