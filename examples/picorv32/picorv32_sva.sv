assert property (
    (picorv32.pcpi_div.instr_div     +
     picorv32.pcpi_div.instr_divu    +
     picorv32.pcpi_div.instr_rem     +
     picorv32.pcpi_div.instr_remu) <= 1
  );

assert property (@(posedge picorv32.clk)
         picorv32.launch_next_insn |-> 
         (picorv32.cpu_state == picorv32.cpu_state_fetch));

assert property (@(posedge picorv32.clk)
         (picorv32.cpu_state == picorv32.cpu_state_trap) |=> 
         (picorv32.cpu_state == picorv32.cpu_state_trap));

assert property (@(posedge clk) disable iff (!resetn)
	instr_any_mul == |{instr_mul, instr_mulh, instr_mulhsu, instr_mulhu}
);
assert property (@(posedge clk) disable iff (!resetn)
	instr_any_mulh == |{instr_mulh, instr_mulhsu, instr_mulhu}
);
assert property (@(posedge clk) disable iff (!resetn)
	instr_rs1_signed == |{instr_mulh, instr_mulhsu}
);
assert property (@(posedge clk) disable iff (!resetn)
	instr_rs2_signed == |{instr_mulh}
);