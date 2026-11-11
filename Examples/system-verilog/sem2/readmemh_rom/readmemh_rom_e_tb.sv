module readmemh_rom_e_tb;
  logic [1:0] addr;
  logic [7:0] q;
  readmemh_rom dut(.addr(addr), .q(q));
  task automatic row(input integer i);
    #1 $display("ROW %0d q=%b", i, q);
  endtask
  initial begin
    addr = 2'b00; row(0);
    addr = 2'b01; row(1);
    addr = 2'b10; row(2);
    addr = 2'b11; row(3);
    addr = 2'bxx; row(4);
    $finish;
  end
endmodule
