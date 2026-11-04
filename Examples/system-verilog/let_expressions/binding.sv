module top;
  int x, result;
  let saved = x;
  let add(a,b) = a+b+x;
  initial begin : outer
    int x;
    x=9;
    top.x=4;
    result=add(.b(2),.a(x));
    $display("binding %0d %0d %0d", saved, result, x);
    begin : inner
      int x;
      x=20;
      $display("nested %0d %0d",saved,add(x,3));
    end
    $display("restored %0d %0d",saved,x);
    $finish;
  end
endmodule
