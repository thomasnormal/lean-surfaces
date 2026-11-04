// STYLE: nested procedural for loops in an always_comb, one XOR-accumulate per partial product
// (cv32e40x's clmul, CORE-V-WALLY's clmul: `for i, for j: r[i+j] ^= a[i] & b[j]`, adapted to the full 2N-1 bits).
// Correct for every N; scored as written. Not yet inside the proof tactics' fragment (README.md, "How people write clmul").
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  always_comb begin
    p = '0;
    for (int i = 0; i < N; i++) begin
      for (int j = 0; j < N; j++) begin
        p[i+j] = p[i+j] ^ (a[i] & b[j]);
      end
    end
  end
endmodule
