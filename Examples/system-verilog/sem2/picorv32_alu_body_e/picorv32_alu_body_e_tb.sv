`timescale 1ns/1ps
module picorv32_alu_body_e_tb;
  logic [31:0] reg_op1;
  logic [31:0] reg_op2;
  logic instr_sub, instr_sra, instr_srai;
  logic [31:0] alu_add_sub, alu_shl, alu_shr;
  logic alu_eq, alu_lts, alu_ltu;

  picorv32_alu_body_e dut (.*);

  task automatic row(input logic [8*24-1:0] name,
                     input logic [31:0] a, input logic [31:0] b,
                     input logic sub, input logic sra, input logic srai);
    begin
      reg_op1 = a; reg_op2 = b;
      instr_sub = sub; instr_sra = sra; instr_srai = srai;
      #1 $display("ROW %0s add_sub=%b eq=%b lts=%b ltu=%b shl=%b shr=%b",
                  name, alu_add_sub, alu_eq, alu_lts, alu_ltu, alu_shl, alu_shr);
    end
  endtask

  initial begin
    reg_op1 = 32'bx; reg_op2 = 32'bx;
    instr_sub = 1'bx; instr_sra = 1'bx; instr_srai = 1'bx;
    #1 $display("ROW first add_sub=%b eq=%b lts=%b ltu=%b shl=%b shr=%b",
                alu_add_sub, alu_eq, alu_lts, alu_ltu, alu_shl, alu_shr);
    row("add_5_3", 32'd5, 32'd3, 1'b0, 1'b0, 1'b0);
    row("sub_5_3", 32'd5, 32'd3, 1'b1, 1'b0, 1'b0);
    row("sra_neg", 32'h80000000, 32'd4, 1'b0, 1'b1, 1'b0);
    row("shr_neg", 32'h80000000, 32'd4, 1'b0, 1'b0, 1'b0);
    row("xz", 32'hxxxx_xxxx, 32'h0000_0001, 1'b0, 1'b0, 1'b0);
    row("srai_flag", 32'h80000000, 32'd4, 1'b0, 1'b0, 1'b1);
    $finish;
  end
endmodule
