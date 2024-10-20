`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     add_wrapp
// Project Name:    Efficient FPGA CNN implementation
// Description:     wrapper around the adder cell with delay chains for the 
//                  side-channel info. Only the B operand side-channel info gets 
//                  propagated
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module add_wrapp
#(
    parameter arith_cfg_t ADD_ARITH_CFG = '{word_wdt:16, fxp_cfg:'{int_wdt:8, frac_wdt:8}, arith_type:FIXED_POINT_GENERIC, arith_satur:1},
    parameter ADD_IN_CYC_LEN = 1,
    parameter ADD_OUT_CYC_LEN = 1
)
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    //data & address 
    input  pipe_data_t add_op_a,   
    input  pipe_data_t add_op_b,   
    output pipe_data_t add_res
);

logic [C_PIPE_DATA_TYPE_WDT:0] side_ch_del;

add_cell //multiplier
#(
.ADD_ARITH_CFG(ADD_ARITH_CFG),
.ADD_IN_CYC_LEN(ADD_IN_CYC_LEN),
.ADD_OUT_CYC_LEN(ADD_OUT_CYC_LEN)
)
add_inst
( 
  .clk(clk),
  .rst_n(rst_n),
  .clk_en(clk_en),
  .add_op_a(add_op_a.data_word), 
  .add_op_b(add_op_b.data_word),
  .add_op_val(add_op_b.data_val),
  .add_res(add_res.data_word),
  .add_res_val(add_res.data_val)
);

del_chain //delay chain for the side-channel information
#(
    .IN_WORD_WDT(C_PIPE_DATA_TYPE_WDT + 1),
    .DEL_CYC_LEN(ADD_IN_CYC_LEN + ADD_OUT_CYC_LEN)
)
data_type_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word({add_op_b.data_last, add_op_b.data_type}),
    .in_word_val(),
    .in_word_del(side_ch_del),
    .in_word_val_del()
);

assign add_res.data_type = side_ch_del[0+:C_PIPE_DATA_TYPE_WDT];
assign add_res.data_last = side_ch_del[C_PIPE_DATA_TYPE_WDT];

endmodule