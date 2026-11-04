// WP-R-D: `always y = a;` never advances time (IEEE 1800-2023 9.2.2.1, a simulation deadlock); slang's ANALYSIS pass reports it (`'always' procedure does not advance time`), Yosys and Verilator read a wire. The extractor already refused the process (`ProceduralBlockSymbol:NoEventControl`) and now also carries slang's own report: `SlangAnalysis:AlwaysWithoutTimingControl`.
module sa_always_notime (
  input  logic a,
  output logic y
);
  always y = a;
endmodule
