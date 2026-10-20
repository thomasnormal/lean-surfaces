module top;
  integer keyed = '{31:1'b1, 23:1'b1, 15:1'b1, 8:1'b1, default:'0};
  logic [7:4] down = '{4:1'b1, 7:1'b0, default:1'bx};
  logic [-2:1] up = '{-2:1'b1, 1:1'b0, default:1'bz};
  initial begin
    $display("keys %h %b %b", keyed, down, up);
    $finish;
  end
endmodule
