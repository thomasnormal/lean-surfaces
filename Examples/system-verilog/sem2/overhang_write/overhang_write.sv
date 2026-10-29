// Round 6 (Xcelium audit cluster P3, lane A, 2026-10-29): a constant indexed
// part-select WRITE that is only PARTLY outside its vector at some parameter
// point. IEEE 1800-2023 11.5.1 writes exactly the in-range bits; Icarus 12.0,
// Yosys 0.53 and slang agree, Xcelium 24.03-s004 DROPS the whole write. The
// model refuses the partly-out point (`ArraySel:partial-overhang`, on the
// msb side `w_hi` at N = 4 and on the lsb side `w_lo` at N = 4). A write wholly
// out of range is a no-op in every tool and stays admitted (`w_lo` at N = 1,
// `w_hi` at N = 6), as does an in-range one.
module overhang_write #(parameter int N = 4) (
  input  logic [3:0] b,
  output logic [7:0] w_hi,
  output logic [7:0] w_lo
);
  always_comb begin
    w_hi = '0;
    w_hi[N+3 +: 4] = b;
  end
  always_comb begin
    w_lo = '0;
    w_lo[N-3 -: 4] = b;
  end
endmodule
