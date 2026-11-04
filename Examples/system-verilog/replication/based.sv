module top;
  logic [84:0] implicit_x = 'hx;
  logic [84:0] implicit_z = 'hz;
  logic [84:0] mixed = 'hx1;
  logic [84:0] sized = 32'hx;
  logic [84:0] casted = 85'('hx);
  logic [31:0] narrow = 'hx;
  logic [84:0] variable_copy;
  bit [84:0] clean = 'hz;
  initial begin
    variable_copy = narrow;
    $display("based %h %h %h", implicit_x, implicit_z, mixed);
    $display("contexts %h %h %h %h", sized, casted, variable_copy, clean);
    $finish;
  end
endmodule
