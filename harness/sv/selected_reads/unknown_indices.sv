module top;
  logic [7:0] source_value;
  integer integer_index;
  logic [3:0] vector_index;
  logic integer_x_bit;
  logic integer_z_bit;
  logic vector_x_bit;
  logic [3:0] x_up_part;
  logic [3:0] z_down_part;
  logic [3:0] vector_up_part;

  initial begin
    source_value = 8'b11010010;
    integer_index = 32'hxxxxxxx1;
    integer_x_bit = source_value[integer_index];
    x_up_part = source_value[integer_index +: 4];
    integer_index = 32'hzzzzzzz1;
    integer_z_bit = source_value[integer_index];
    z_down_part = source_value[integer_index -: 4];
    vector_index = 4'b0x01;
    vector_x_bit = source_value[vector_index];
    vector_up_part = source_value[vector_index +: 4];
    $display("unknown-indices=[%b][%b][%b][%b][%b][%b]", integer_x_bit,
             integer_z_bit, vector_x_bit, x_up_part, z_down_part, vector_up_part);
    if ((integer_x_bit === 1'bx) && (integer_z_bit === 1'bx) &&
        (vector_x_bit === 1'bx) && (x_up_part === 4'bxxxx) &&
        (z_down_part === 4'bxxxx) && (vector_up_part === 4'bxxxx))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
