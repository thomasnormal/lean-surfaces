// The reduction XNOR `~^v` / `^~v` (IEEE 1800-2023 11.4.9): 1 when the number of 1 bits is even and
// every bit is known, x when any bit is x/z. WP-L2 (2026-10-30): both spellings, a vector, a part
// select, and a single bit (~^ of one bit is its complement).
module xnor_red #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic         p,
  output logic         r1,     // ~^a
  output logic         r2,     // ^~a
  output logic         r3,     // ~^a[N-1:1] (a part select, one bit shorter)
  output logic         r4      // ~^p
);
  assign r1 = ~^a;
  assign r2 = ^~a;
  assign r3 = ~^a[N-1:1];
  assign r4 = ~^p;
endmodule
