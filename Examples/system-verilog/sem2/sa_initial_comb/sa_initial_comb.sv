// WP-R-D: `initial` plus `always_comb` writers of one variable: slang's ANALYSIS pass reports `multiple-always-assigns` (IEEE 1800-2023 9.2.2.2: a variable written by an always_comb cannot be written by any other process), Xcelium `*E,MULAXX`; the extractor and svGolf's `fourstate` admitted it until 2026-11-01 and the Lean loader refused it only for lack of an `Initial` process kind. The extractor now refuses on slang's own report: `SlangAnalysis:MultipleAlwaysAssigns`.
module sa_initial_comb (
  input  logic a,
  output logic y
);
  initial y = 1'b0;
  always_comb y = a;
endmodule
