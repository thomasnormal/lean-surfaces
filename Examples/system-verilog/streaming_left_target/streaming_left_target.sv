/*
:name: streaming_left_target
:description: IEEE 1800-2023 11.4.14 -- fixed-size left streaming reverses source chunks into target leaves
:tags: 11.4.14 streaming left unpack target
:type: simulation
*/
module top;
  bit [31:0] source;
  bit [7:0] le[4];

  initial begin
    source = 32'h4142_4344;
    {<<8 {le[0], le[1], le[2], le[3]}} = source;
    if (le[0] !== 8'h44 || le[1] !== 8'h43 ||
        le[2] !== 8'h42 || le[3] !== 8'h41)
      $display("FAIL %h %h %h %h", le[0], le[1], le[2], le[3]);
    else
      $display("PASS");
    $finish;
  end
endmodule
