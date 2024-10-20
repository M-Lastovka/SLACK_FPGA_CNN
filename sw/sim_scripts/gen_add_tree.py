
"""
Author: Martin Lastovka, @RWTH DSP 
Project: Efficient FPGA CNN implementation for 5G physical layer - Master Thesis @ RWTH DSP
Desc: Generate adder tree using the adder primitive. Supports operand count which is not a power of 2. 

"""

#!/usr/bin/env python3
import os
import cnn_params as cnn_p
import numpy as np

def gen_delay(op, res, name, del_len):
    return f"""del_chain
    #(
        .IN_WORD_WDT(C_ARITH_WORD_LEN),
        .DEL_CYC_LEN({del_len})
    )
    {name}
    (
        .clk(clk),
        .rst_n(rst_n),
        .clk_en(clk_en),
        .in_word({op}),
        .in_word_val(),
        .in_word_del({res}), 
        .in_word_val_del()
    );\n"""

def gen_add(op_a, op_b, res, name):
    return f"""add_cell
    #(
    .ADD_ARITH_CFG(C_ADD_ARITH_CFG),
    .ADD_IN_CYC_LEN(C_ADD_FXP_IN_CYC_LEN),
    .ADD_OUT_CYC_LEN(C_ADD_FXP_OUT_CYC_LEN)
    )
    {name}
    ( 
      .clk(clk),
      .rst_n(rst_n),
      .clk_en(clk_en),
      .add_op_a({op_a}), 
      .add_op_b({op_b}),
      .add_op_val(),
      .add_res({res}),
      .add_res_val()
    );\n"""

def gen_add_tree(add_tree_file_path='add_tree.sv'):
    buff = ""
    #print module header, ports etc.
    buff = buff + \
    f"""    `timescale 1ns / 1ps
    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Institution:     RWTH Aachen - DSP chair
    // Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
    // Module Name:     add_tree
    // Project Name:    Efficient FPGA CNN implementation
    // Description:     Adder tree for non-power of two element count. Automatically generated, do not edit manually. Operand count = {cnn_p.C_VECT_SIZE}
    // Synthesizable:   Yes
    ///////////////////////////////////////////////////////////////////////////////////////////////
    
    import arith_pckg::*;
    import proc_pipe_pckg::*;
    
    module add_tree
    (
        //clk & reset & enable
        input  logic clk,
        input  logic rst_n,
        input  logic clk_en,
        //data & address 
        input  logic [C_ARITH_WORD_LEN-1:0] add_tree_ops[C_ADD_TREE_OP_CNT-1:0],
        output logic [C_ARITH_WORD_LEN-1:0] add_tree_res
    );\n"""

    #print the adders, stage by stage
    add_tree_stage_cnt = int(np.ceil(np.log2(cnn_p.C_VECT_SIZE)))
    this_stage_op_cnt = cnn_p.C_VECT_SIZE

    for i in range(add_tree_stage_cnt + 1): #generate the intermediate values
        buff = buff + f"    logic [C_ARITH_WORD_LEN-1:0] add_tree_stage_{i}[{this_stage_op_cnt-1}:0];\n"
        buff = buff + f"    logic [C_ARITH_WORD_LEN-1:0] add_tree_stage_{i}_q[{this_stage_op_cnt-1}:0];\n"
        this_stage_op_cnt = int(np.ceil(this_stage_op_cnt/2))

    buff = buff + \
            """    always_comb begin 
        foreach(add_tree_stage_0[i])
            add_tree_stage_0[i] = add_tree_ops[i];
        end\n
            """

    this_stage_op_cnt = cnn_p.C_VECT_SIZE
    for i in range(add_tree_stage_cnt):
        for j in range(int(np.ceil(this_stage_op_cnt/2.0))):
            if(2**j == this_stage_op_cnt - 1 and this_stage_op_cnt != 2): #delay chain
                buff = buff + gen_delay(op=f"add_tree_stage_{i}[{2 * j}]", res=f"add_tree_stage_{i + 1}_q[{j}]", name=f"add_tree_del_chain_{i}_{j}", del_len="C_ADD_FXP_CYC_LEN")
            else: #adder
                buff = buff + gen_add(op_a=f"add_tree_stage_{i}[{2 * j}]", op_b=f"add_tree_stage_{i}[{2 * j + 1}]", res=f"add_tree_stage_{i + 1}_q[{j}]", name=f"add_tree_add_cell_{i}_{j}")
            #inter-stage delay chain
            buff = buff + gen_delay(op=f"add_tree_stage_{i + 1}_q[{j}]", res=f"add_tree_stage_{i + 1}[{j}]", name=f"add_tree_interstage_del_chain_{i}_{j}", del_len="C_ADD_TREE_LVL_DEL_CYC_LEN")
        this_stage_op_cnt = int(np.ceil(this_stage_op_cnt/2))

    buff = buff + f"    assign add_tree_res =  add_tree_stage_{add_tree_stage_cnt}[0];\n"
    buff = buff + "    endmodule\n"

    #write to a file
    with open(os.path.join(os.getcwd(), add_tree_file_path), 'w') as file:
        file.write(buff)

gen_add_tree()

    