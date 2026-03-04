assert property (@(posedge i2c_master_top.wb_clk_i) (i2c_master_top.wb_cyc_i && i2c_master_top.wb_stb_i && !i2c_master_top.wb_ack_o) |-> ##1 i2c_master_top.wb_ack_o);
assert property (@(posedge i2c_master_top.wb_clk_i)
  (i2c_master_top.wb_we_i && i2c_master_top.wb_ack_o) |-> i2c_master_top.wb_wacc);
assert property (@(posedge i2c_master_top.wb_clk_i)
  i2c_master_top.wb_adr_i == 3'b111 |-> ##1 i2c_master_top.wb_dat_o == 0);