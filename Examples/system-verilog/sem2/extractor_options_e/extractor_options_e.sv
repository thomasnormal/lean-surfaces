`ifdef ENABLED
module extractor_options_e(input logic x, output logic y);
  initial $error("check");
  assign y = x;
endmodule
`else
module extractor_options_e(input logic x, output logic y);
  assign y = 1'b0;
endmodule
`endif
