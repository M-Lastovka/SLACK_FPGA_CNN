`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     tb_top
// Project Name:    Efficient FPGA CNN implementation
// Description:     Testbench top
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

`include "tb_macro_def.svh"
`include "tb_axi_driver.sv"
`include "tb_axis_driver.sv"
`include "tb_axis_monitor.sv"

import arith_pckg::*;
import proc_pipe_pckg::*;
import axi_if_pckg::*;
import tb_pckg::*;
import regmap_pckg::*;
import regmap_reg_pckg::*;

import axi4stream_vip_pkg::*;
import axi_vip_pkg::*;
import tb_top_block_axi_vip_0_0_pkg::*;
import tb_top_block_axi4stream_vip_0_0_pkg::*;
import tb_top_block_axi4stream_vip_1_0_pkg::*;

module tb_top;

logic        clk = 0;
logic        rst_n = 0;
bit          halt_tb = 0;

//generator and monitor objects
tb_axis_monitor      host_stream_monitor;
tb_axis_driver       host_stream_driver;
tb_axi_driver        host_mm_driver;

//external (to DUT) axi stream master and slaves objects
tb_top_block_axi4stream_vip_1_0_slv_t  s_axis_ext_agent;
tb_top_block_axi4stream_vip_0_0_mst_t  m_axis_ext_agent;
tb_top_block_axi_vip_0_0_mst_t         m_axi_ext_agent;

axil_wr_trans_t axil_wr_trans;
axil_rd_trans_t axil_rd_trans;

s_axis_trans_t s_axis_trans;
m_axis_trans_t m_axis_trans;

stream_trans_lst_t h2c_trans_lst;
stream_trans_lst_t c2h_trans_lst;

int h2c_wrote_bytes;
int mm_new_offset;
int mm_offset = 0;
int curr_seq_index = -1;
int read_bytes;
bit accel_busy = 0;
logic [C_S_AXI_DATA_WDT-1:0] axil_rd_data_temp;

// Clock generation
initial begin
  forever begin
    #1.25ns 
    clk = ~clk;  
  end
end

initial begin
  $timeformat(-9, 4, " ns", 14);
end

// Reset generation
initial begin
  rst_n = 0;
  #5ns rst_n = 1;
end

initial begin

  host_mm_driver = new(m_axi_ext_agent);
  host_mm_driver.init_m_axi_ext_agent();

  host_stream_driver = new(m_axis_ext_agent);
  host_stream_driver.init_m_axis_ext_agent();

  host_stream_monitor = new(s_axis_ext_agent);
  host_stream_monitor.init_s_axis_ext_agent();

  read_sim_ctrl(C_TEST_CTRL_PATH, h2c_trans_lst, c2h_trans_lst);

  #50ns;

  //read regmap state
  axil_rd_trans.axil_rd_start_addr = 0;
  axil_rd_trans.axil_rd_len        = 8;
  host_mm_driver.axi_rd_block(axil_rd_trans);

  fork
    begin //H2C
      foreach(h2c_trans_lst[i]) begin
        if(curr_seq_index != h2c_trans_lst[i].seq_index) begin //beginning of new sequence, load regmap
          do begin //first check if the DUT is not busy
            host_mm_driver.axi_rd_single(axil_rd_data_temp, C_STAT_REG_ADDR);
            accel_busy = (axil_rd_data_temp & C_STAT_REG_TENS_TRANS_SEQ_BUSY_MASK) >> C_STAT_REG_TENS_TRANS_SEQ_BUSY_LSB;
          end while(accel_busy);
          curr_seq_index++;
          host_mm_driver.axi_bin_file(C_TEST_MM_PATH, mm_offset, 0, 0, XIL_AXI_PAYLOAD_RETURN, mm_new_offset);
          mm_offset = mm_new_offset; //next sequence start where we left off
        end
        //then transfer stream
        host_stream_driver.axis_write_bin_file(C_TEST_H2C_STREAM_PATH, h2c_trans_lst[i].offset, h2c_trans_lst[i].len, read_bytes);
        `display_verb("TB_TOP", $sformatf("Dumped H2C transfer to DUT, offset: %d, len: %d, tensor name: %s", h2c_trans_lst[i].offset, h2c_trans_lst[i].len, h2c_trans_lst[i].tens_name), VERB_LOW)
      end
    end

    begin //C2H
      foreach(c2h_trans_lst[i]) begin
        host_stream_monitor.axis_dump_bin_file(C_TEST_C2H_STREAM_PATH);
        `display_verb("TB_TOP", $sformatf("Dumped C2H transfer to %s, offset: %d, len: %d, tensor name: %s", C_TEST_C2H_STREAM_PATH, c2h_trans_lst[i].offset, c2h_trans_lst[i].len, c2h_trans_lst[i].tens_name), VERB_LOW)
      end
    end
  join

  //read regmap state
  axil_rd_trans.axil_rd_start_addr = 0;
  axil_rd_trans.axil_rd_len        = 100;
  host_mm_driver.axi_rd_block(axil_rd_trans);

end

tb_top_block_wrapper dut_wrapp
(
    .clk(clk),
    .rst_n(rst_n)
);


endmodule