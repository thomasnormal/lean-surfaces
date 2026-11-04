// Round 6 (Xcelium audit cluster T1, lane A, 2026-10-29): a run-time bit
// select whose INDEX is wider than 32 bits. IEEE 1800-2023 11.5.1 evaluates
// the index in a self-determined context and reads x for an out-of-range one;
// the model takes the whole value (Yosys 0.53 `prep; eval` agrees). Xcelium
// 24.03-s004 (warning BIGWBS), Icarus 12.0 and Verilator 5.042 truncate the
// index to its low 32 bits and read a defined bit (`a - 3` at `a = 2^32 + 5`
// over a 42-bit `a`: 2^32 + 2 is out of range, its low 32 bits are 2). The
// model refuses a run-time index wider than 32 bits (`Select:wide-index`),
// read and write alike; at most 32 bits stays admitted (N = 8, N = 30).
module wide_index #(parameter int N = 8) (
  input  logic [N+1:0] a,
  input  logic [7:0]   v,
  input  logic         b,
  output logic         o,
  output logic [7:0]   w
);
  assign o = v[a - 3];
  always_comb begin
    w = '0;
    w[a] = b;
  end
endmodule
