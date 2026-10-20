// SPDX-License-Identifier: Apache-2.0
// Case-array widening needs its own validated conversion rule.
module top;
  logic signed [3:0] narrow[2:0] = '{-1,2,3};
  logic signed [7:0] equal_width[2:0] = '{-1,2,3};
  logic signed [3:0] small_subject = -1;
  logic signed [7:0] subject = -1;
  int result;
  initial begin
    $display("elements %0d %0d %0d",narrow[2],narrow[1],narrow[0]);
    $display("inside %b", subject inside {narrow});
    result=0; case(subject) inside narrow:result=1; endcase
    $display("case_narrow %0d",result);
    result=0; case(subject) inside narrow[2]:result=1; endcase
    $display("case_scalar %0d",result);
    result=0; case(subject) inside equal_width:result=1; endcase
    $display("case_equal %0d",result);
    result=0; case(small_subject) inside narrow:result=1; endcase
    $display("case_small %0d",result);
    result=0; case(subject) inside narrow, 8'shff:result=1; endcase
    $display("case_second_scalar %0d",result);
    $finish;
  end
endmodule
