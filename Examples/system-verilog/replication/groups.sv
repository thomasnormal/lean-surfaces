module top;
  logic [7:0] group = {2{2'b10, 2'bxz}};
  logic [11:0] nested = {2{{3{2'b10}}}};
  logic [15:0] mixed = {4'h9, {2{4'h3}}, 4'ha};
  initial begin
    $display("groups %b %b %h", group, nested, mixed);
    $finish;
  end
endmodule
