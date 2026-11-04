module top;
  localparam int ZERO = 0;
  logic [7:0] tail;
  logic [7:0] empty_then_tail;
  logic [15:0] nested = {2{{ZERO{4'b1xz0}}, 8'h3c}};
  initial begin
    tail = 8'ha5;
    empty_then_tail = {{ZERO{4'b1xz0}}, tail};
    $display("zero %h %h", empty_then_tail, nested);
    $finish;
  end
endmodule
