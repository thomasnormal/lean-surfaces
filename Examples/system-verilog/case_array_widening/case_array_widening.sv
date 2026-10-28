/*
:name: case_array_widening
:description: IEEE 1800-2023 §12.5.4 case-inside arrays widen each scalar item to the subject width
:tags: 12.5.4
:type: simulation
*/
module top;
  logic signed [3:0] narrow[2:0] = '{-1, 2, 3};
  logic signed [7:0] subject = -1;
  int result;
  initial begin
    result = 0;
    case (subject) inside
      narrow: result = 1;
      default: result = 2;
    endcase
    if (result !== 1)
      $display("FAIL");
    else
      $display("PASS");
    $finish;
  end
endmodule
