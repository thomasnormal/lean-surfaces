// Clean-room time-zero initializer for canonical source-shaped memory.
module memory_initial_canonical_e #(parameter integer W = 8, parameter integer P = 3,
    parameter integer INIT_ZERO = 1) (
    input logic [P-1:0] idx,
    output logic [W-1:0] q
);
    logic [W-1:0] s [0:P-1];
    integer i;
    initial begin
      if (INIT_ZERO) begin
        for (i = 0; i < P; i = i + 1)
          s[i] = 0;
      end
      s[0] = 8'hA5;
    end
    assign q = s[idx];
endmodule
