// Phase-2 probe: blocking select write in always_comb (default + bit
// override); an x/z index write is a no-op (the default survives).
module t2_combw (
    input  logic [2:0] i,
    input  logic [7:0] base,
    input  logic b,
    output logic [7:0] y
);
  always_comb begin
    y = base;
    y[i] = b;
  end
endmodule
