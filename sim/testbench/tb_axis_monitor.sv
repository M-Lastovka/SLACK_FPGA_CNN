`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     tb_axis_monitor
// Project Name:    Efficient FPGA CNN implementation
// Description:     Monitor for AXIS, utilizing Xilinx AXIS VIP
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

`include "tb_macro_def.svh"

import axi_if_pckg::*;
import tb_pckg::*;

import axi4stream_vip_pkg::*;
import tb_top_block_axi4stream_vip_1_0_pkg::*;

class tb_axis_monitor;

local string tb_axis_monitor_name;
local tb_top_block_axi4stream_vip_1_0_slv_t s_axis_ext_agent; //AXIS VIP instance
local axi4stream_ready_gen ready_gen;
local xil_axi4stream_ready_gen_policy_t tready_policy = XIL_AXI4STREAM_READY_GEN_RANDOM;
local bit first_dump_file_write = 1;

function new
(
    tb_top_block_axi4stream_vip_1_0_slv_t s_axis_ext_agent,
    xil_axi4stream_ready_gen_policy_t tready_policy = XIL_AXI4STREAM_READY_GEN_RANDOM,
    string tb_axis_monitor_name = "tb_axis_monitor"
);
    this.tb_axis_monitor_name = tb_axis_monitor_name;
    this.s_axis_ext_agent = s_axis_ext_agent; //AXIS VIP instance
    this.tready_policy = tready_policy;
    `display_verb(this.tb_axis_monitor_name, $sformatf("AXIS monitor class instantiated with name %s ,ready policy: %s", this.tb_axis_monitor_name, tready_policy.name()), VERB_MID)    
endfunction

task init_s_axis_ext_agent();
    this.s_axis_ext_agent = new("s_axis_ext_agent", `s_axis_ext_if_path);
    this.s_axis_ext_agent.start_slave();
    this.ready_gen = this.s_axis_ext_agent.driver.create_ready("ready_gen");
    this.ready_gen.set_ready_policy(this.tready_policy);
    this.s_axis_ext_agent.driver.send_tready(this.ready_gen);
endtask 

task automatic axis_rd_block
(
    ref s_axis_trans_t s_axis_trans,
    input int word_cnt_lim = 0
);
    
    axi4stream_monitor_transaction   s_axis_vip_rd_trans;
    logic [7:0] data_beat_unpack[C_M_TKEEP_WDT];
    logic [C_M_TDATA_WDT-1:0] data_beat_pack;
    bit keep_beat_unpack[C_M_TKEEP_WDT];
    logic [C_M_TKEEP_WDT-1:0] keep_beat_pack;
    s_axis_tdata_t s_axis_tdata = '{};
    s_axis_tkeep_t s_axis_tkeep = '{};
    int beat_cnt = 0;

    if(s_axis_trans.s_axis_tdata.size() != s_axis_trans.s_axis_tkeep.size() & s_axis_trans.s_axis_tkeep.size() != 0) begin
        `error_verb(this.tb_axis_monitor_name, "Keep and data shall be of the same size, or the former is of zero size!")
    end

    `display_verb(this.tb_axis_monitor_name, $sformatf("Started AXIS read, word count: %d, tlast %s", s_axis_trans.s_axis_tdata.size(), s_axis_trans.s_axis_tlast ? "enabled" : "disabled"), VERB_HIGH)

    do begin

        this.s_axis_ext_agent.monitor.item_collected_port.get(s_axis_vip_rd_trans);
        s_axis_vip_rd_trans.get_data(data_beat_unpack);
        s_axis_vip_rd_trans.get_keep(keep_beat_unpack);
        foreach(data_beat_unpack[i]) begin
            data_beat_pack[i * 8 +: 8] = data_beat_unpack[i];
            keep_beat_pack[i] = keep_beat_unpack[i];
        end
        `display_verb(this.tb_axis_monitor_name, $sformatf("Received new AXIS read beat, data: 0x%h, keep 0b%b", data_beat_pack, keep_beat_pack), VERB_HIGH)
        s_axis_tdata.push_back(data_beat_pack);
        s_axis_tkeep.push_back(keep_beat_pack);
        beat_cnt++;

    end while (!s_axis_vip_rd_trans.get_last() & s_axis_trans.s_axis_tlast | beat_cnt == word_cnt_lim & !s_axis_trans.s_axis_tlast);

    s_axis_trans.s_axis_tdata = s_axis_tdata;
    s_axis_trans.s_axis_tkeep = s_axis_tkeep;

    `display_verb(this.tb_axis_monitor_name, $sformatf("Finished AXIS read, read words: %d", beat_cnt), VERB_HIGH)
    
endtask 

task axis_dump_bin_file //dump AXIS block to a binary file
(
    string file_name, 
    int word_cnt_lim = 0,
    bit tlast = 1
); 

    int fd = 0;
    s_axis_trans_t s_axis_trans;
    logic [C_M_TDATA_WDT-1:0] s_axis_tdata_rev;
    logic [C_EXT_DATA_WORD_WDT-1:0] ext_word;
    int s_axis_tdata_val_bytes;
    logic [C_M_TDATA_WDT-1:0] temp;
    bit[7:0] byte2write;
    int n_bytes = 0;
    
    `display_verb(this.tb_axis_monitor_name, $sformatf("Dumping AXIS block from the DUT to a file: %s", file_name), VERB_LOW)
    
    //on first write, we clear the dump file, for the subsequent writes, we append
    if(this.first_dump_file_write) begin
        fd = $fopen(file_name, "wb");
        this.first_dump_file_write = 0;
    end else begin
        fd = $fopen(file_name, "ab");
    end
    
    s_axis_trans.s_axis_tlast = tlast;
    
    assert(fd) else $fatal (0, "File for dumping the DUT AXIS data could not be opened, exiting simulation!");
    
    this.axis_rd_block(s_axis_trans, word_cnt_lim);

    foreach(s_axis_trans.s_axis_tdata[i]) begin
        s_axis_tdata_val_bytes = $countones(s_axis_trans.s_axis_tkeep[i]);
        if(C_M_TDATA_WDT == C_BYTE_WDT) begin //special case
            $fwrite(fd, "%c", s_axis_trans.s_axis_tdata[i]);
            n_bytes += 1;
        end else begin
            s_axis_tdata_rev =  {<<C_EXT_DATA_WORD_WDT{s_axis_trans.s_axis_tdata[i]}}; //switch word order
            for(int j = 0; j < C_M_TDATA_WDT/C_EXT_DATA_WORD_WDT; j++) begin
                ext_word = s_axis_tdata_rev[j*C_EXT_DATA_WORD_WDT +: C_EXT_DATA_WORD_WDT];
                if(C_MONITOR_REV_ENDIAN)
                    ext_word = {<<C_BYTE_WDT{ext_word}}; //switch endiannity
                for(int k = 0; k < (s_axis_tdata_val_bytes > C_EXT_DATA_WORD_WDT/C_BYTE_WDT ? C_EXT_DATA_WORD_WDT/C_BYTE_WDT : s_axis_tdata_val_bytes); k++) begin
                    byte2write = ext_word[k*C_BYTE_WDT +: C_BYTE_WDT];
                    $fwrite(fd, "%c", byte2write);
                    n_bytes += 1;
                end 
                s_axis_tdata_val_bytes = s_axis_tdata_val_bytes - (s_axis_tdata_val_bytes > C_EXT_DATA_WORD_WDT/C_BYTE_WDT ? C_EXT_DATA_WORD_WDT/C_BYTE_WDT : s_axis_tdata_val_bytes);
            end
        end
    end
    
    $fclose(fd);
    
    `display_verb(this.tb_axis_monitor_name, $sformatf("Done dumping AXIS data from the DUT, bytes written: %d, closing file", n_bytes), VERB_LOW)

endtask

endclass