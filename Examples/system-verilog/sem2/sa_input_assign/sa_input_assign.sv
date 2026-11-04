// WP-R-D: slang's ANALYSIS pass reports `cannot assign to input port 'a'` (IEEE 1800-2023 23.3.3.2); `Compilation.getAllDiagnostics()` does not contain it, so until 2026-11-01 only the Lean `driversOk` clause 3 (`PortConn:driver`) refused this design. The extractor now refuses on slang's own report: `SlangAnalysis:InputPortAssign`.
module sa_input_assign (
  input  logic a,
  input  logic b,
  output logic y
);
  assign a = b;
  assign y = a;
endmodule
