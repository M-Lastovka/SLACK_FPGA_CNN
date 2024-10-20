`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     tb_axi_driver
// Project Name:    Efficient FPGA CNN implementation
// Description:     Driver for AXI-lite, utilizing Xilinx AXI VIP
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

`include "tb_macro_def.svh"

import axi_if_pckg::*;
import tb_pckg::*;

import axi_vip_pkg::*;
import tb_top_block_axi_vip_0_0_pkg::*;

class tb_axi_driver;

local string tb_axi_driver_name;
local tb_top_block_axi_vip_0_0_mst_t m_axi_ext_agent; //AXI VIP instance
local axi_ready_gen rready_gen;
local xil_axi_ready_gen_policy_t rready_policy;
local axi_ready_gen bready_gen;
local xil_axi_ready_gen_policy_t bready_policy;

function new
(
    tb_top_block_axi_vip_0_0_mst_t m_axi_ext_agent,
    xil_axi_ready_gen_policy_t rready_policy = XIL_AXI_READY_GEN_RANDOM,
    xil_axi_ready_gen_policy_t bready_policy = XIL_AXI_READY_GEN_RANDOM,
    string tb_axi_driver_name = "tb_axi_driver"
);
    this.tb_axi_driver_name = tb_axi_driver_name;
    this.m_axi_ext_agent = m_axi_ext_agent; //AXI VIP instance
    this.rready_policy = rready_policy;
    this.bready_policy = bready_policy;  
    `display_verb(this.tb_axi_driver_name, $sformatf("AXI driver class instantiated with name %s", this.tb_axi_driver_name), VERB_MID)    
endfunction

task init_m_axi_ext_agent();
    this.m_axi_ext_agent = new("m_axi_ext_agent", `m_axi_ext_if_path);
    this.m_axi_ext_agent.start_master();
    this.rready_gen = m_axi_ext_agent.rd_driver.create_ready("rready_gen");
    this.rready_gen.set_ready_policy(this.rready_policy);
    this.bready_gen = m_axi_ext_agent.wr_driver.create_ready("bready_gen");
    this.bready_gen.set_ready_policy(this.bready_policy);
endtask 

task automatic axi_wr_block
(
    axil_wr_trans_t axil_wr_trans,
    xil_axi_driver_return_policy_t driver_return_policy = XIL_AXI_PAYLOAD_RETURN
);

    axi_transaction m_axi_vip_wr_trans;
    xil_axi_ulong   m_axi_vip_waddr = axil_wr_trans.axil_wr_start_addr;
    xil_axi_size_t  m_axi_vip_wdata_size = xil_axi_size_t'(C_S_AXI_STRB_WDT);

    if(axil_wr_trans.axil_wr_tdata.size() != axil_wr_trans.axil_wr_tstrb.size() & axil_wr_trans.axil_wr_tstrb.size() != 0) begin
        `error_verb(this.tb_axi_driver_name, "Strobe and data shall be of the same size, or the former is of zero size!")
    end

    `display_verb(this.tb_axi_driver_name, $sformatf("Start AXI write @start addr: 0x%0h, word count: %d", m_axi_vip_waddr, axil_wr_trans.axil_wr_tdata.size()), VERB_HIGH)

    fork
        foreach(axil_wr_trans.axil_wr_tdata[i]) begin //write
            m_axi_vip_wr_trans = this.m_axi_ext_agent.wr_driver.create_transaction("m_axi_vip_wr_trans");
            assert(m_axi_vip_wr_trans.randomize());
            //setup
            m_axi_vip_wr_trans.set_driver_return_item_policy(driver_return_policy);
            m_axi_vip_wr_trans.set_addr_delay(3);
            m_axi_vip_wr_trans.set_data_insertion_delay(3);
            m_axi_vip_wr_trans.set_beat_delay(0, 0);
            m_axi_vip_wr_trans.set_write_cmd(m_axi_vip_waddr + 4*i, XIL_AXI_BURST_TYPE_INCR, 0, 0, m_axi_vip_wdata_size);
            for(int j = 0; j < m_axi_vip_wr_trans.get_len()+1; j++) begin
                m_axi_vip_wr_trans.set_data_beat(j, axil_wr_trans.axil_wr_tdata[i]);
                m_axi_vip_wr_trans.set_strb_beat(j, axil_wr_trans.axil_wr_tstrb.size() == 0 ? '1 : axil_wr_trans.axil_wr_tstrb[i]);
            end
            this.m_axi_ext_agent.wr_driver.send(m_axi_vip_wr_trans);
        end

        foreach(axil_wr_trans.axil_wr_tdata[i]) begin //response
            if(driver_return_policy == XIL_AXI_PAYLOAD_RETURN) begin
                this.m_axi_ext_agent.wr_driver.wait_rsp(m_axi_vip_wr_trans);
            end
        end
    join

    `display_verb(this.tb_axi_driver_name, $sformatf("Done AXI write @start addr: 0x%0h, word count: %d", m_axi_vip_waddr, axil_wr_trans.axil_wr_tdata.size()), VERB_HIGH)

    endtask //automatic

 task automatic axi_rd_block
 (
     ref axil_rd_trans_t axil_rd_trans,
     input xil_axi_driver_return_policy_t driver_return_policy = XIL_AXI_PAYLOAD_RETURN
 );

    axi_transaction m_axi_vip_rd_trans;
    xil_axi_ulong m_axi_vip_raddr = axil_rd_trans.axil_rd_start_addr;
    xil_axi_size_t m_axi_vip_rdata_size = xil_axi_size_t'(C_S_AXI_STRB_WDT);
    xil_axi_data_beat m_axi_vip_rdata_beat[];
    axil_tdata_t axil_rd_tdata = '{};
    int rd_len;

    `display_verb(this.tb_axi_driver_name, $sformatf("Start AXI read @start addr: 0x%0h, word count: %d", m_axi_vip_raddr, axil_rd_trans.axil_rd_len), VERB_HIGH)
    rd_len = axil_rd_trans.axil_rd_len;

    fork
        for(int i = 0; i < rd_len; i++) begin //read
            m_axi_vip_rd_trans = this.m_axi_ext_agent.rd_driver.create_transaction("m_axi_vip_rd_trans");
            assert(m_axi_vip_rd_trans.randomize()); //randomize
            //setup
            m_axi_vip_rd_trans.set_driver_return_item_policy(driver_return_policy);
            m_axi_vip_rd_trans.set_read_cmd(m_axi_vip_raddr + 4*i, XIL_AXI_BURST_TYPE_INCR, 0, 0, m_axi_vip_rdata_size);
            this.m_axi_ext_agent.rd_driver.send(m_axi_vip_rd_trans);
        end
        for(int j = 0; j < rd_len; j++) begin //read
            if(driver_return_policy == XIL_AXI_PAYLOAD_RETURN) begin //response
                this.m_axi_ext_agent.rd_driver.wait_rsp(m_axi_vip_rd_trans);
                m_axi_vip_rdata_beat = new[m_axi_vip_rd_trans.get_len()+1];
                for(int k = 0; k < m_axi_vip_rd_trans.get_len() + 1; k++) begin
                    m_axi_vip_rdata_beat[k] = m_axi_vip_rd_trans.get_data_beat(k);
                    axil_rd_tdata.push_back(m_axi_vip_rdata_beat[k]);
                end
            end
        end
    join

    axil_rd_trans.axil_rd_tdata = axil_rd_tdata;

    `display_verb(this.tb_axi_driver_name, $sformatf("Done AXI read @start addr: 0x%0h, word count: %d", m_axi_vip_raddr, axil_rd_trans.axil_rd_len), VERB_HIGH)

endtask

task automatic axi_wr_single
(
     logic [C_S_AXI_DATA_WDT-1:0] axil_wr_data,
     logic [C_S_AXI_ADDR_WDT-1:0] axil_wr_addr
);

    axil_wr_trans_t axil_wr_trans;

    axil_wr_trans.axil_wr_start_addr = axil_wr_addr;
    axil_wr_trans.axil_wr_tdata.push_back(axil_wr_data);
    axil_wr_trans.axil_wr_tstrb = '{};
    this.axi_wr_block(axil_wr_trans);

endtask

task automatic axi_rd_single
(
    ref logic [C_S_AXI_DATA_WDT-1:0] axil_rd_data,
    input logic [C_S_AXI_ADDR_WDT-1:0] axil_rd_addr
);

    axil_rd_trans_t axil_rd_trans;

    axil_rd_trans.axil_rd_start_addr = axil_rd_addr;
    axil_rd_trans.axil_rd_len        = 1;
    this.axi_rd_block(axil_rd_trans);

    axil_rd_data = axil_rd_trans.axil_rd_tdata.pop_front();
    
endtask

//write/read the memory transactions specified in a binary file (specified by offset and length, by default we keep reading
task automatic axi_bin_file
(
    string file_name,
    int file_trans_offset = 0,
    int file_trans_cnt = 0,
    bit file_ignore = 0,
    xil_axi_driver_return_policy_t driver_return_policy = XIL_AXI_PAYLOAD_RETURN,
    output int file_trans_end_offset
);

    int fd = 0;
    logic [C_MM_TRANS_WDT-1:0] temp_trans;
    logic [7:0] mm_dir_buffer;
    logic [C_S_AXI_ADDR_WDT-1:0] mm_addr_buffer;
    logic [C_S_AXI_DATA_WDT-1:0] mm_data_buffer;
    logic [C_S_AXI_STRB_WDT-1:0] mm_str_buffer;
    int scan_r = 0;
    int fseek_ret_val;
    int read_mm_trans_cnt = 0;
    bit read_until_eof = file_trans_cnt == 0; //by default we read until end of file
    axil_wr_trans_t axil_wr_trans;
    axil_rd_trans_t axil_rd_trans;
    `display_verb(this.tb_axi_driver_name, $sformatf("Generating AXI write transactions by reading a file: %s", file_name), VERB_LOW)
    fd = $fopen(file_name, "rb");
    assert(fd) else $fatal (0, "File could not be opened, exiting simulation!");

    //first skip the transactions before the offset
    fseek_ret_val = $fseek(fd, file_trans_offset*C_MM_TRANS_WDT/8, 0);
    while((read_until_eof & !$feof(fd)) | (!read_until_eof & read_mm_trans_cnt < file_trans_cnt)) begin
        scan_r = $fread(mm_dir_buffer, fd, , 1); 
        scan_r = $fread(mm_addr_buffer, fd, , C_S_AXI_ADDR_WDT/8); 
        scan_r = $fread(mm_data_buffer, fd, , C_S_AXI_DATA_WDT/8);
        scan_r = $fread(mm_str_buffer,  fd, , 1);
        if(scan_r != 0)
            read_mm_trans_cnt++;
        //check for EOB symbol
        if({mm_dir_buffer, mm_addr_buffer, mm_data_buffer, mm_str_buffer} == '0)
            break;
        //switch byte order
        if(C_MM_REV_ENDIAN) begin
            mm_addr_buffer = {<<8{mm_addr_buffer}};
            mm_data_buffer = {<<8{mm_data_buffer}}; 
            mm_str_buffer  = {<<8{mm_str_buffer}};
        end    
        //put transaction on the line
        if(!file_ignore) begin
            if(mm_dir_buffer) begin
                `display_verb(this.tb_axi_driver_name, $sformatf("New write AXI-lite transaction: (addr: 0x%h data: 0x%h strobe: 0x%h)", mm_addr_buffer, mm_data_buffer, mm_str_buffer), VERB_HIGH)
                axil_wr_trans.axil_wr_tdata.push_back(mm_data_buffer);
                axil_wr_trans.axil_wr_tstrb.push_back(mm_str_buffer[C_S_AXI_STRB_WDT-1:0]);
                axil_wr_trans.axil_wr_start_addr = mm_addr_buffer;
                this.axi_wr_block(axil_wr_trans);
                axil_wr_trans.axil_wr_tdata = '{};
                axil_wr_trans.axil_wr_tstrb = '{};
            end else begin
                `display_verb(this.tb_axi_driver_name, $sformatf("New read AXI-lite transaction: (addr: 0x%h)", mm_addr_buffer), VERB_HIGH)
                axil_rd_trans.axil_rd_start_addr = mm_addr_buffer;
                axil_rd_trans.axil_rd_len        = 1;
                this.axi_rd_block(axil_rd_trans);
            end
        end
    end
    file_trans_end_offset = read_mm_trans_cnt + file_trans_offset;
    `display_verb(this.tb_axi_driver_name, $sformatf("Done writing AXI transactions by reading a file: %s", file_name), VERB_LOW)
    $fclose(fd);

endtask

endclass