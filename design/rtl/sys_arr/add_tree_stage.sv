`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     sys_arr_cell
// Project Name:    Efficient FPGA CNN implementation
// Description:     Cell of the systolic array, features a register holding the stationary
//                  value, forwarding port to the next cell and a multiplier which computes
//                  product of stationary and moving value and forwards it to the adder tree.
//
//                  Single stage of the adder tree
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module add_tree_stage
#(
    parameter ADD_TREE_OP_CNT = 2,
    parameter ADD_TREE_STAGE_OP_CNT = 2,
    parameter ADD_TREE_STAGE_RES_CNT = 1
)
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    //data & address 
    input  pipe_data_t sys_arr_data_add_tree_ops[ADD_TREE_OP_CNT-1:0],
    output pipe_data_t sys_arr_add_tree_res[ADD_TREE_STAGE_RES_CNT-1:0]
);

localparam ADD_TREE_STAGE_OP_PAIR_CNT = $floor(ADD_TREE_OP_CNT/2);

pipe_data_t sys_arr_add_tree_res_i[ADD_TREE_STAGE_OP_PAIR_CNT-1:0];

genvar i;
generate
    for(i = 0; i < ADD_TREE_STAGE_OP_PAIR_CNT; i++) begin
        add_cell
        #(
        .ADD_ARITH_CFG(C_ADD_ARITH_CFG),
        .ADD_IN_CYC_LEN(C_ADD_FXP_IN_CYC_LEN),
        .ADD_OUT_CYC_LEN(C_ADD_FXP_OUT_CYC_LEN)
        )
        add_inst
        ( 
          .clk(clk),
          .rst_n(rst_n),
          .clk_en(clk_en),
          .add_op_a(sys_arr_data_add_tree_ops[2*i].data_word), 
          .add_op_b(sys_arr_data_add_tree_ops[2*i+1].data_word),
          .add_op_val(sys_arr_data_add_tree_ops[2*i+1].data_word_val),
          .add_res(sys_arr_add_tree_res_i[i].data_word),
          .add_res_val(sys_arr_add_tree_res_i[i].data_word_val)
        );

        del_chain //delay chain before the results enter the next stage
        #(
            .IN_WORD_WDT(C_PIPE_DATA_WDT),
            .DEL_CYC_LEN(C_ADD_TREE_LVL_DEL_CYC_LEN)
        )
        add_tree_lvl_del_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word(sys_arr_add_tree_res_i[i].data_word),
            .in_word_val(sys_arr_add_tree_res_i[i].data_word_val),
            .in_word_del(sys_arr_add_tree_res[i].data_word), 
            .in_word_val_del(sys_arr_add_tree_res[i].data_word_val)
        );
    end
    if(ADD_TREE_OP_CNT % 2) begin //the number of operands was not even in this level, generate a delay chain for the last operand
        del_chain
        #(
            .IN_WORD_WDT(C_PIPE_DATA_WDT),
            .DEL_CYC_LEN(C_ADD_FXP_CYC_LEN + C_ADD_TREE_LVL_DEL_CYC_LEN)
        )
        add_tree_odd_op_del_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word(sys_arr_data_add_tree_ops[ADD_TREE_OP_CNT-1].data_word),
            .in_word_val(sys_arr_data_add_tree_ops[ADD_TREE_OP_CNT-1].data_word_val),
            .in_word_del(sys_arr_add_tree_res[ADD_TREE_STAGE_RES_CNT-1].data_word),
            .in_word_val_del(sys_arr_add_tree_res[ADD_TREE_STAGE_RES_CNT-1].data_word_val)
        );
    end
endgenerate

endmodule