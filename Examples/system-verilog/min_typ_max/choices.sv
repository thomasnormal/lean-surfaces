module top;
  logic[3:0] narrow;
  logic signed[15:0] signed_value;
  int selected_value,width_a,width_b;
  initial begin
    narrow=(32'h11:8'h22:16'h33);
    signed_value=(8'sh80:8'sh81:8'sh82);
    selected_value=(33:22:11);
    $display("choices %0d %h %0d",selected_value,narrow,signed_value);
    width_a=($bits(4'b1):$bits(8'b1):$bits(16'b1));
    width_b=($bits(1):$bits(8'b1):$bits(16'b1));
    $display("widths %0d %0d",width_a,width_b);
    $finish;
  end
endmodule
