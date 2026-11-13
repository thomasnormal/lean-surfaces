module tb;
  logic [31:0] reg_op1, reg_op2, alu_add_sub;
  logic instr_beq, instr_bne, instr_bge, instr_bgeu, instr_xor, instr_or, instr_and;
  logic is_slti_blt_slt, is_sltiu_bltu_sltu, is_alu, is_compare;
  logic alu_eq, alu_lts, alu_ltu;
  wire alu_out_0;
  wire [31:0] alu_out;
  picorv32_alu_case_canonical_e dut (.*);
  initial begin
    reg_op1=32'd5; reg_op2=32'd3; instr_beq=1; instr_bne=0; instr_bge=0; instr_bgeu=0;
    instr_xor=0; instr_or=0; instr_and=0; is_slti_blt_slt=0; is_sltiu_bltu_sltu=0;
    is_alu=0; is_compare=1; alu_eq=1; alu_lts=0; alu_ltu=0; alu_add_sub=32'd8; #1;
    $display("ROW 0 alu_out=%b", alu_out);
    instr_beq=0; instr_xor=1; is_compare=0; #1;
    $display("ROW 1 alu_out=%b", alu_out);
    $finish;
  end
endmodule
