module picorv32_alu_case_canonical_e #(
    parameter bit TWO_CYCLE_COMPARE = 1'b0
) (
    input logic [31:0] reg_op1,
    input logic [31:0] reg_op2,
    input logic instr_beq, instr_bne, instr_bge, instr_bgeu,
    input logic instr_xor, instr_or, instr_and,
    input logic is_slti_blt_slt, is_sltiu_bltu_sltu,
    input logic is_alu, is_compare,
    input logic alu_eq, alu_lts, alu_ltu,
    input logic [31:0] alu_add_sub,
    output logic alu_out_0,
    output logic [31:0] alu_out
);
  always_comb begin
    alu_out_0 = 'x;
    case (1'b1)
      instr_beq: alu_out_0 = alu_eq;
      instr_bne: alu_out_0 = !alu_eq;
      instr_bge: alu_out_0 = !alu_lts;
      instr_bgeu: alu_out_0 = !alu_ltu;
      is_slti_blt_slt && (!TWO_CYCLE_COMPARE || !(instr_beq || instr_bne || instr_bge || instr_bgeu)):
        alu_out_0 = alu_lts;
      is_sltiu_bltu_sltu && (!TWO_CYCLE_COMPARE || !(instr_beq || instr_bne || instr_bge || instr_bgeu)):
        alu_out_0 = alu_ltu;
    endcase
    alu_out = 'x;
    case (1'b1)
      is_alu: alu_out = alu_add_sub;
      is_compare: alu_out = {{31{1'b0}}, alu_out_0};
      instr_xor: alu_out = reg_op1 ^ reg_op2;
      instr_or: alu_out = reg_op1 | reg_op2;
      instr_and: alu_out = reg_op1 & reg_op2;
    endcase
  end
endmodule
