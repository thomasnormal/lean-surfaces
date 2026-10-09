module top;
  integer integer_source;
  time time_source;
  int base_value;
  logic integer_high_bit;
  logic time_high_bit;
  logic [3:0] integer_high_part;
  logic [3:0] integer_low_part;
  logic [3:0] integer_above_part;
  logic [3:0] time_high_part;
  logic [3:0] time_above_part;

  initial begin
    integer_source = 32'h89abcdef;
    time_source = 64'hfedcba9876543210;
    integer_high_bit = integer_source[31];
    time_high_bit = time_source[63];
    integer_high_part = integer_source[31:28];
    integer_low_part = integer_source[3:0];
    base_value = 30;
    integer_above_part = integer_source[base_value +: 4];
    time_high_part = time_source[63:60];
    base_value = 62;
    time_above_part = time_source[base_value +: 4];
    $display("integer-sources=[%b][%b][%b][%b][%b][%b][%b]", integer_high_bit,
             time_high_bit, integer_high_part, integer_low_part,
             integer_above_part, time_high_part, time_above_part);
    if ((integer_high_bit === 1'b1) && (time_high_bit === 1'b1) &&
        (integer_high_part === 4'b1000) && (integer_low_part === 4'b1111) &&
        (integer_above_part === 4'bxx10) && (time_high_part === 4'b1111) &&
        (time_above_part === 4'bxx11))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: ebe6707675bebccccd4b5615 TOOL:	xrun(64)	24.03-s004 2026-10-09T21:44:13Z args=-ii_val
