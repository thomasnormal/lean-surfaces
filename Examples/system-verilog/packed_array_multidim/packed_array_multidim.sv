/* Canonical, upward, and enum packed arrays flatten to contiguous vectors. */
module top;
  logic [1:0][3:0] a;
  logic [0:1][0:3] b;
  typedef enum bit [1:0] { STATE_A = 2'd0, STATE_B = 2'd1,
                           STATE_C = 2'd2 } state_t;
  state_t [3:0] states;

  initial begin
    a = 8'hAB;
    b = 8'hA5;
    states = '0;
    states[0] = STATE_A;
    states[1] = STATE_B;
    states[2] = STATE_C;
    if (a[1] === 4'hA && a[0] === 4'hB &&
        a[1][3] === 1'b1 && a[0][0] === 1'b1 &&
        b[0] === 4'hA && b[1] === 4'h5 &&
        b[0][0] === 1'b1 && b[1][3] === 1'b1 &&
        states[0] === STATE_A && states[1] === STATE_B && states[2] === STATE_C)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
