module top;
  logic signed [3:0] small_value=-1;
  logic signed [7:0] wider=-1;
  logic [3:0] unsigned_small_value=15;
  logic [7:0] dynamic_item=8'b1z01_x0z1;
  logic [7:0] dynamic_subject=8'b1001_x001;
  logic [64:0] wide=65'bz;
  int code;
  initial begin
    code=0;
    casez(small_value) 4'sd0: code=1; wider: code=2; default: code=3; endcase
    $display("signed %0d",code);
    casez(unsigned_small_value) wider: code=4; default: code=5; endcase
    $display("mixed %0d",code);
    casez(4'bx001) 4'b0001: code=6; 4'bx001: code=7; default: code=8; endcase
    $display("exact_x %0d",code);
    casez(dynamic_subject) dynamic_item: code=9; default: code=10; endcase
    $display("dynamic_z %0d",code);
    dynamic_subject=8'b1001_1001;
    casex(dynamic_subject) dynamic_item: code=11; default: code=12; endcase
    $display("dynamic_x %0d",code);
    casez(wide) 65'd1: code=13; 65'd0: code=14; default: code=15; endcase
    $display("wide %0d",code);
    code=16;
    casez(2'bx0) 2'b10: code=17; endcase
    $display("no_match %0d",code);
    casez(2'bz1)
      default: code=18;
      2'b01,2'b11: begin
        casex(2'bx0) 2'b00: code=19; default: code=20; endcase
      end
      2'bz1: code=21;
    endcase
    $display("first_nested %0d",code);
    $finish;
  end
endmodule
