module top;
  localparam int N = 2;
  logic signed [3:0] narrow = -1;
  logic signed [11:0] widened = {N{narrow}};
  logic [3:0] truncated = {2{4'h9}};
  bit [7:0] clean = {4{2'bxz}};
  logic [3:0] repeated_unbased = {4{'1}};
  logic [15:0] chosen = {2{(1'b1 ? 8'hab : 8'hcd)}};
  initial begin
    $display("contexts %h %h %b %b %h", widened, truncated, clean, repeated_unbased, chosen);
    $finish;
  end
endmodule
