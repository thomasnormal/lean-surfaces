// Two temporaries, each written before it is read (ADMITTED).
// Admitted by the always_comb self-read guard (LeanModels/Sv/CombGuard2.lean).
module acg_two_temps (
  input  logic [2:0] a, b, c,
  output logic [2:0] y
);
  logic [2:0] t1, t2;
  always_comb begin
    t1 = a & b;
    t2 = t1 | c;
    y = t2 ^ t1;
  end
endmodule
