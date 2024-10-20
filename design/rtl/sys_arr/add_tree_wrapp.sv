`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     add_tree_wrapp
// Project Name:    Efficient FPGA CNN implementation
// Description:     wrapper for the adder tree utilizing the adder cell
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module add_tree_wrapp
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    //data & address 
    input  pipe_data_t sys_arr_data_add_tree_ops[C_ADD_TREE_OP_CNT-1:0],
    output pipe_data_t sys_arr_add_tree_res
);

localparam C_ADD_TREE_OP_CNT_POW2 = round_npow2(C_ADD_TREE_OP_CNT);

logic [C_ADD_ARITH_CFG.word_wdt-1:0] add_tree_ops [C_ADD_TREE_OP_CNT-1:0];

//prepare inputs
always_comb begin
    foreach(add_tree_ops[i])
        add_tree_ops[i] = sys_arr_data_add_tree_ops[i].data_word;
end

add_tree add_tree_inst
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .add_tree_ops(add_tree_ops),
    .add_tree_res(sys_arr_add_tree_res.data_word)
);

logic [C_PIPE_DATA_TYPE_WDT+1:0] sys_arr_data_side_ch;
logic [C_PIPE_DATA_TYPE_WDT+1:0] sys_arr_data_side_ch_del;

always_comb begin //prepare the inputs and handle outputs
    sys_arr_data_side_ch[0 +: C_PIPE_DATA_TYPE_WDT] = sys_arr_data_add_tree_ops[0].data_type;
    sys_arr_data_side_ch[C_PIPE_DATA_TYPE_WDT] = 1'b1;
    for(int i = 0; i < C_ADD_TREE_OP_CNT; i++)
        sys_arr_data_side_ch[C_PIPE_DATA_TYPE_WDT] = sys_arr_data_side_ch[C_PIPE_DATA_TYPE_WDT] & sys_arr_data_add_tree_ops[i].data_val;
    sys_arr_data_side_ch[C_PIPE_DATA_TYPE_WDT+1] = sys_arr_data_add_tree_ops[0].data_last;
    
    sys_arr_add_tree_res.data_val  = sys_arr_data_side_ch_del[C_PIPE_DATA_TYPE_WDT];
    sys_arr_add_tree_res.data_last      = sys_arr_data_side_ch_del[C_PIPE_DATA_TYPE_WDT+1];
    sys_arr_add_tree_res.data_type      = sys_arr_data_side_ch_del[0 +: C_PIPE_DATA_TYPE_WDT];
end

//side-channel information delay chain
del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_TYPE_WDT + 2),
    .DEL_CYC_LEN(C_ADD_TREE_DEL_CYC_LEN)
)
add_tree_side_ch_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(sys_arr_data_side_ch),
    .in_word_val(),
    .in_word_del(sys_arr_data_side_ch_del),
    .in_word_val_del()
);

endmodule