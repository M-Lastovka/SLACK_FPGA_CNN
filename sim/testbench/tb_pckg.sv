`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     tb_pckg
// Project Name:    Efficient FPGA CNN implementation
// Description:     testbench package
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

`include "tb_macro_def.svh"

package tb_pckg;
import axi_if_pckg::*;

typedef enum 
{
    VERB_LOW,
    VERB_MID,
    VERB_HIGH
} verb_lvl;

parameter verb_lvl GLOB_VERB_LVL = VERB_HIGH;

typedef logic [C_M_TDATA_WDT-1:0] s_axis_tdata_t[$];
typedef logic [C_M_TKEEP_WDT-1:0] s_axis_tkeep_t[$];
typedef struct
{
    s_axis_tdata_t s_axis_tdata;
    s_axis_tkeep_t s_axis_tkeep;
    bit s_axis_tlast;
} s_axis_trans_t;

typedef logic [C_S_TDATA_WDT-1:0] m_axis_tdata_t[$];
typedef logic [C_S_TKEEP_WDT-1:0] m_axis_tkeep_t[$];
typedef struct
{
    m_axis_tdata_t m_axis_tdata;
    m_axis_tkeep_t m_axis_tkeep;
    bit m_axis_tlast;
} m_axis_trans_t;

typedef logic [C_S_AXI_DATA_WDT-1:0] axil_tdata_t[$];
typedef logic [C_S_AXI_STRB_WDT-1:0] axil_tstrb_t[$];
typedef struct
{
    axil_tdata_t axil_wr_tdata;
    axil_tstrb_t axil_wr_tstrb;
    logic [C_S_AXI_ADDR_WDT-1:0] axil_wr_start_addr;
} axil_wr_trans_t;

typedef struct
{
    logic [C_S_AXI_ADDR_WDT-1:0] axil_rd_start_addr;
    int  axil_rd_len;
    axil_tdata_t axil_rd_tdata;
} axil_rd_trans_t;

parameter C_MM_TRANS_WDT = (C_S_AXI_ADDR_WDT + C_S_AXI_DATA_WDT + 16);
parameter C_MM_REV_ENDIAN = 0;

//TODO: autogenerate
parameter string C_PROJ_PATH = "c:\\Users\\lasto\\Desktop\\born_to_kill\\test_git_repo\\eff_fpga_cnn_impl_master_thesis";
parameter string C_TEST_MM_PATH = {C_PROJ_PATH, "\\sw\\sim_scripts\\test_mm.bin"};
parameter string C_TEST_H2C_STREAM_PATH = {C_PROJ_PATH, "\\sw\\sim_scripts\\test_h2c_stream.bin"};
parameter string C_TEST_C2H_STREAM_PATH = {C_PROJ_PATH, "\\sw\\sim_scripts\\test_c2h_stream.bin"};
parameter string C_TEST_CTRL_PATH = {C_PROJ_PATH, "\\sw\\sim_scripts\\test_ctrl.txt"};

parameter C_DRIVER_REV_ENDIAN = 0;
parameter C_MONITOR_REV_ENDIAN = 1;

typedef struct
{
    int offset;
    int len;
    string tens_name;
    int seq_index;
} stream_trans_t;

typedef stream_trans_t stream_trans_lst_t[$];

task automatic read_sim_ctrl(string test_ctrl_file_path, ref stream_trans_lst_t h2c_trans_lst, ref stream_trans_lst_t c2h_trans_lst);
    
    int fd = 0;
    int scan_r = 0;

    string trans_dir;
    int offset;
    int len;
    string tens_name;
    int seq_index;

    stream_trans_t h2c_trans_new;
    stream_trans_t c2h_trans_new;

    `display_verb("TB_TOP: ", $sformatf("Reading sim control file: %s", test_ctrl_file_path), VERB_LOW)
    fd = $fopen(test_ctrl_file_path, "r");
    assert(fd) else $fatal(1, "File for reading sim control could not be opened, exiting sim!");
    while(!$feof(fd)) begin
        scan_r = $fscanf(fd, "%s,", trans_dir);
        scan_r = $fscanf(fd, "%d,", offset);
        scan_r = $fscanf(fd, "%d,", len);
        scan_r = $fscanf(fd, "%s,", tens_name);
        scan_r = $fscanf(fd, "%d\n", seq_index);
        if(trans_dir == "H2C") begin
            h2c_trans_new.offset      = offset;
            h2c_trans_new.len         = len;
            h2c_trans_new.tens_name   = tens_name;
            h2c_trans_new.seq_index   = seq_index;
            h2c_trans_lst.push_back(h2c_trans_new);
            `display_verb("TB_TOP", $sformatf("Pushed new H2C transfer, offset: %d, len: %d, tensor name: %s, sequence index: %d", offset, len, tens_name, seq_index), VERB_MID)
        end else if(trans_dir == "C2H") begin
            c2h_trans_new.offset      = offset;
            c2h_trans_new.len         = len;
            c2h_trans_new.tens_name   = tens_name;
            c2h_trans_new.seq_index   = seq_index;
            c2h_trans_lst.push_back(c2h_trans_new);
            `display_verb("TB_TOP", $sformatf("Pushed new C2H transfer, offset: %d, len: %d, tensor name: %s, sequence index: %d", offset, len, tens_name, seq_index), VERB_MID)
        end else begin
            assert(0) else $fatal("Unknown symbol for stream dir in the sim control file!");
        end
    end
    `display_verb("TB_TOP: ", $sformatf("Done reading sim control file: %s", test_ctrl_file_path), VERB_LOW)

endtask
endpackage