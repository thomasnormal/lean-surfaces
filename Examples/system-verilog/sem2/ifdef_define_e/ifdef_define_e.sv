// Clean-room preprocessor witness for IEEE 1800-2023 §22.5.
// The extractor receives the same FEATURE definition as the simulator.
`ifdef FEATURE
module ifdef_define_e(input logic a, output logic y);
  assign y = a;
endmodule
`else
module ifdef_define_e(input logic a, output logic y);
  assign y = ~a;
endmodule
`endif
