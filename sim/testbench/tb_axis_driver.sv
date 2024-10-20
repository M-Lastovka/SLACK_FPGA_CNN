`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     tb_axis_driver
// Project Name:    Efficient FPGA CNN implementation
// Description:     Driver for AXIS, utilizing Xilinx AXIS VIP
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

`include "tb_macro_def.svh"

import axi_if_pckg::*;
import tb_pckg::*;

import axi4stream_vip_pkg::*;
import tb_top_block_axi4stream_vip_0_0_pkg::*;

class tb_axis_driver;

local string tb_axis_driver_name;
local tb_top_block_axi4stream_vip_0_0_mst_t m_axis_ext_agent; //AXIS VIP instance

function new
(
    tb_top_block_axi4stream_vip_0_0_mst_t m_axis_ext_agent,
    string tb_axis_driver_name = "tb_axis_driver"
);
    this.tb_axis_driver_name = tb_axis_driver_name;
    this.m_axis_ext_agent = m_axis_ext_agent; //AXIS VIP instance
    `display_verb(this.tb_axis_driver_name, $sformatf("AXIS driver class instantiated with name %s", this.tb_axis_driver_name), VERB_MID)    
endfunction

task init_m_axis_ext_agent();
    this.m_axis_ext_agent = new("m_axis_ext_agent", `m_axis_ext_if_path);
    this.m_axis_ext_agent.start_master();
endtask 

task automatic axis_wr_block
(
    m_axis_trans_t m_axis_trans
);
    
    axi4stream_transaction  m_axis_vip_wr_trans;
    bit wr_keep_unpacked[C_S_TKEEP_WDT-1:0];
    
    if(m_axis_trans.m_axis_tdata.size() != m_axis_trans.m_axis_tkeep.size() & m_axis_trans.m_axis_tkeep.size() != 0) begin
        `error_verb(this.tb_axis_driver_name, "Keep and data shall be of the same size, or the former is of zero size!")
    end
    
    `display_verb(this.tb_axis_driver_name, $sformatf("Start AXIS write word count: %d", m_axis_trans.m_axis_tdata.size()), VERB_HIGH)
    
    foreach(m_axis_trans.m_axis_tdata[i]) begin //write
        m_axis_vip_wr_trans = this.m_axis_ext_agent.driver.create_transaction("m_axis_vip_wr_trans");
        assert(m_axis_vip_wr_trans.randomize());
        //setup
        m_axis_vip_wr_trans.set_delay($urandom_range(0,3)); //TODO timing model
        m_axis_vip_wr_trans.set_data_beat(m_axis_trans.m_axis_tdata[i]);
        foreach(wr_keep_unpacked[j])
            if(m_axis_trans.m_axis_tkeep.size() == 0)
                wr_keep_unpacked[j] = 1'b1;
            else
                wr_keep_unpacked[j] = m_axis_trans.m_axis_tkeep[i][j];
        m_axis_vip_wr_trans.set_keep(wr_keep_unpacked);
        m_axis_vip_wr_trans.set_last((i == m_axis_trans.m_axis_tdata.size() - 1) & m_axis_trans.m_axis_tlast);
        this.m_axis_ext_agent.driver.send(m_axis_vip_wr_trans);
    end
    
    `display_verb(this.tb_axis_driver_name, $sformatf("Done AXIS write word count: %d", m_axis_trans.m_axis_tdata.size()), VERB_HIGH)
    
endtask //automatic

//write the contents of a binary file (specified by offset and length) to the DUT through AXIS
task automatic axis_write_bin_file
(
    string file_name,
    int file_offset,
    int bytes_to_read,
    output int read_bytes
);

    int fd = 0;
    int data_beat_val_bytes;
    logic [C_S_TDATA_WDT-1:0] data_beat_buffer = '0;
    logic [C_S_TKEEP_WDT-1:0] keep_beat_buffer = '0;
    m_axis_tdata_t m_axis_tdata = '{};
    m_axis_tkeep_t m_axis_tkeep = '{};
    m_axis_trans_t m_axis_trans;

    int scan_r = 0;
    int read_word_cnt = 0;
    int fseek_ret_val;

    `display_verb(this.tb_axis_driver_name, $sformatf("Generating AXIS write transaction by reading %d bytes from file: %s at offset: %d", bytes_to_read, file_name, file_offset), VERB_MID)

    fd = $fopen(file_name, "rb");

    assert(fd) else $fatal (1, "File for generating AXIS write transaction could not be opened, exiting simulation!");

    //first skip the bytes before offset
    fseek_ret_val = $fseek (fd, file_offset, 0);

    while((read_bytes < bytes_to_read & bytes_to_read > 0) | (!$feof(fd) & bytes_to_read == 0)) begin
        scan_r = $fread(data_beat_buffer, fd, , C_S_TDATA_WDT/C_BYTE_WDT);
        //switch byte order
        if(C_DRIVER_REV_ENDIAN)
            data_beat_buffer = {<<8{data_beat_buffer}};
        //shift if valid bytes are expected to be MSB aligned
        data_beat_buffer = data_beat_buffer << C_BYTE_WDT*(C_S_TDATA_WDT/C_BYTE_WDT - scan_r);
        if(scan_r != 0) begin
            m_axis_tdata.push_back(data_beat_buffer);
            //resolve keep signal
            if(scan_r < C_S_TDATA_WDT/C_BYTE_WDT)
                data_beat_val_bytes = scan_r;
            else
                data_beat_val_bytes = (C_S_TDATA_WDT/C_BYTE_WDT + read_bytes <= bytes_to_read) ? C_S_TDATA_WDT/C_BYTE_WDT : C_S_TDATA_WDT/C_BYTE_WDT + read_bytes - bytes_to_read;
            keep_beat_buffer = '0; 
            for(int i = 0; i < data_beat_val_bytes; i++)
                keep_beat_buffer[i] = 1'b1;
            m_axis_tkeep.push_back(keep_beat_buffer);
            `display_verb(this.tb_axis_driver_name, $sformatf("New data beat: 0x%h, keep beat: 0b%b read from the binary stream file", data_beat_buffer, keep_beat_buffer), VERB_HIGH)
            read_word_cnt++;
            read_bytes += scan_r;
        end
    end

    `display_verb(this.tb_axis_driver_name, $sformatf("Done reading file, total number of bytes read: %d", read_bytes), VERB_LOW)

    m_axis_trans.m_axis_tdata = m_axis_tdata;
    m_axis_trans.m_axis_tkeep = m_axis_tkeep;
    m_axis_trans.m_axis_tlast = 1'b1;
    this.axis_wr_block(m_axis_trans);

endtask

endclass