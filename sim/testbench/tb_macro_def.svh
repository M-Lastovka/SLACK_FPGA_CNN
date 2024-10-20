`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     tb_macro_def
// Project Name:    Efficient FPGA CNN implementation
// Description:     Testbench macros
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

//path to AXIS components
`define m_axi_ext_if_path  tb_top.dut_wrapp.tb_top_block_i.axi_vip_0.inst.IF
`define m_axis_ext_if_path tb_top.dut_wrapp.tb_top_block_i.axi4stream_vip_0.inst.IF
`define s_axis_ext_if_path tb_top.dut_wrapp.tb_top_block_i.axi4stream_vip_1.inst.IF

`define display_verb(prefix, string_info, verb) \
    if(verb <= GLOB_VERB_LVL) begin \
        $display("@time %t: %s: %s", $time(), prefix, string_info); \
    end \

`define error_verb(prefix, string_info) \
    $error("@time %t: %s: %s", $time(), prefix, string_info); \
