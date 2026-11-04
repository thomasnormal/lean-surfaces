// IEEE 1800-2023 12.7.3, 12.8 and 11.5.1.
module top;
  int arr[-1:1];
  bit [3:1] mem[2:0];
  int i=99, j=88;
  int count=0, trace=0;
  initial begin
    foreach(arr[i]) begin arr[i]=i+2; $display("unpacked %0d %0d",i,arr[i]); end
    foreach(mem[i,j]) begin
      count++;
      if(j==2) continue;
      trace=trace*10+i;
      if(i==1) break;
    end
    $display("multi %0d %0d outer %0d %0d",count,trace,i,j);
    foreach(mem[,j]) $display("skip %0d",j);
    count=0;
    foreach(mem[]) count++;
    $display("empty %0d",count);
    count=0;
    foreach(mem[i,j]) begin
      $display("tuple %0d %0d",i,j);
      count++;
    end
    $display("tuples %0d",count);
    count=0;
    repeat(2) foreach(arr[i]) foreach(arr[i]) begin
      count++;
      break;
    end
    $display("nested_reentry %0d",count);
    mem[2]=3'b1xz;
    foreach(mem[,j]) $display("packed %0d %b",j,mem[2][j]);
    i=-1;
    $display("invalid_negative %b",mem[2][i]);
    i=32'h80000000;
    $display("invalid_min %b",mem[2][i]);
    i=32'h7fffffff;
    $display("invalid_max %b",mem[2][i]);
    i='x;
    $display("invalid_unknown %b",mem[2][i]);
    $finish;
  end
endmodule
