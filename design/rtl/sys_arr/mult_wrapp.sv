`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     mult_wrapp
// Project Name:    Efficient FPGA CNN implementation
// Description:     wrapper around the multiplication cell with delay chains for the 
//                  side-channel info. Only the B operand side-channel info gets 
//                  propagated
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module mult_wrapp
#(
    parameter arith_cfg_t MULT_ARITH_CFG = '{word_wdt:16, fxp_cfg:'{int_wdt:8, frac_wdt:8}, arith_type:FIXED_POINT_GENERIC, arith_satur:1},
    parameter MULT_IN_CYC_LEN = 1,
    parameter MULT_OUT_CYC_LEN = 1
)
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    //data & address 
    input  pipe_data_t mult_op_a,   
    input  pipe_data_t mult_op_b,   
    output pipe_data_t mult_res
);

logic [C_PIPE_DATA_TYPE_WDT:0] side_ch_del;

mult_cell //multiplier
#(
.MULT_ARITH_CFG(MULT_ARITH_CFG),
.MULT_IN_CYC_LEN(MULT_IN_CYC_LEN),
.MULT_OUT_CYC_LEN(MULT_OUT_CYC_LEN)
)
mult_inst
( 
  .clk(clk),
  .rst_n(rst_n),
  .clk_en(clk_en),
  .mult_op_a(mult_op_a.data_word), 
  .mult_op_b(mult_op_b.data_word),
  .mult_op_val(mult_op_b.data_val),
  .mult_res(mult_res.data_word),
  .mult_res_val(mult_res.data_val)
);

del_chain //delay chain for the side-channel information
#(
    .IN_WORD_WDT(C_PIPE_DATA_TYPE_WDT + 1),
    .DEL_CYC_LEN(MULT_IN_CYC_LEN + MULT_OUT_CYC_LEN)
)
data_type_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word({mult_op_b.data_last, mult_op_b.data_type}),
    .in_word_val(),
    .in_word_del(side_ch_del),
    .in_word_val_del()
);

assign mult_res.data_type = side_ch_del[0+:C_PIPE_DATA_TYPE_WDT];
assign mult_res.data_last = side_ch_del[C_PIPE_DATA_TYPE_WDT];

endmodule