// Round 6 (Xcelium audit cluster P1, lane A, 2026-10-29): a constant indexed
// part-select READ that is only PARTLY outside its vector at some parameter
// point. IEEE 1800-2023 11.5.1 reads x in exactly the out-of-range bits
// (`a[10 +: 4]` on [11:0] is {xx, a[11:10]}); Icarus 12.0, Yosys 0.53 and slang
// agree, Xcelium 24.03-s004 reads the WHOLE select as x. The model refuses
// the partly-out point (`ArraySel:partial-overhang`). In range (N = 3) and
// wholly out of range (N = 5: x in every tool) stay admitted.
module overhang_read #(parameter int N = 3) (
  input  logic [11:0] a,
  output logic [3:0]  y
);
  assign y = a[N*3-2 +: 4];
endmodule
