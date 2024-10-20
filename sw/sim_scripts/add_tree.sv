    `timescale 1ns / 1ps
    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Institution:     RWTH Aachen - DSP chair
    // Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
    // Module Name:     add_tree
    // Project Name:    Efficient FPGA CNN implementation
    // Description:     Adder tree for non-power of two element count. Automatically generated, do not edit manually. Operand count = 5
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
    );
    logic [C_ARITH_WORD_LEN-1:0] add_tree_stage_0[4:0];
    logic [C_ARITH_WORD_LEN-1:0] add_tree_stage_0_q[4:0];
    logic [C_ARITH_WORD_LEN-1:0] add_tree_stage_1[2:0];
    logic [C_ARITH_WORD_LEN-1:0] add_tree_stage_1_q[2:0];
    logic [C_ARITH_WORD_LEN-1:0] add_tree_stage_2[1:0];
    logic [C_ARITH_WORD_LEN-1:0] add_tree_stage_2_q[1:0];
    logic [C_ARITH_WORD_LEN-1:0] add_tree_stage_3[0:0];
    logic [C_ARITH_WORD_LEN-1:0] add_tree_stage_3_q[0:0];
    always_comb begin 
        foreach(add_tree_stage_0[i])
            add_tree_stage_0[i] = add_tree_ops[i];
        end

            add_cell
    #(
    .ADD_ARITH_CFG(C_ADD_ARITH_CFG),
    .ADD_IN_CYC_LEN(C_ADD_FXP_IN_CYC_LEN),
    .ADD_OUT_CYC_LEN(C_ADD_FXP_OUT_CYC_LEN)
    )
    add_tree_add_cell_0_0
    ( 
      .clk(clk),
      .rst_n(rst_n),
      .clk_en(clk_en),
      .add_op_a(add_tree_stage_0[0]), 
      .add_op_b(add_tree_stage_0[1]),
      .add_op_val(),
      .add_res(add_tree_stage_1_q[0]),
      .add_res_val()
    );
del_chain
    #(
        .IN_WORD_WDT(C_ARITH_WORD_LEN),
        .DEL_CYC_LEN(C_ADD_TREE_LVL_DEL_CYC_LEN)
    )
    add_tree_interstage_del_chain_0_0
    (
        .clk(clk),
        .rst_n(rst_n),
        .clk_en(clk_en),
        .in_word(add_tree_stage_1_q[0]),
        .in_word_val(),
        .in_word_del(add_tree_stage_1[0]), 
        .in_word_val_del()
    );
add_cell
    #(
    .ADD_ARITH_CFG(C_ADD_ARITH_CFG),
    .ADD_IN_CYC_LEN(C_ADD_FXP_IN_CYC_LEN),
    .ADD_OUT_CYC_LEN(C_ADD_FXP_OUT_CYC_LEN)
    )
    add_tree_add_cell_0_1
    ( 
      .clk(clk),
      .rst_n(rst_n),
      .clk_en(clk_en),
      .add_op_a(add_tree_stage_0[2]), 
      .add_op_b(add_tree_stage_0[3]),
      .add_op_val(),
      .add_res(add_tree_stage_1_q[1]),
      .add_res_val()
    );
del_chain
    #(
        .IN_WORD_WDT(C_ARITH_WORD_LEN),
        .DEL_CYC_LEN(C_ADD_TREE_LVL_DEL_CYC_LEN)
    )
    add_tree_interstage_del_chain_0_1
    (
        .clk(clk),
        .rst_n(rst_n),
        .clk_en(clk_en),
        .in_word(add_tree_stage_1_q[1]),
        .in_word_val(),
        .in_word_del(add_tree_stage_1[1]), 
        .in_word_val_del()
    );
del_chain
    #(
        .IN_WORD_WDT(C_ARITH_WORD_LEN),
        .DEL_CYC_LEN(C_ADD_FXP_CYC_LEN)
    )
    add_tree_del_chain_0_2
    (
        .clk(clk),
        .rst_n(rst_n),
        .clk_en(clk_en),
        .in_word(add_tree_stage_0[4]),
        .in_word_val(),
        .in_word_del(add_tree_stage_1_q[2]), 
        .in_word_val_del()
    );
del_chain
    #(
        .IN_WORD_WDT(C_ARITH_WORD_LEN),
        .DEL_CYC_LEN(C_ADD_TREE_LVL_DEL_CYC_LEN)
    )
    add_tree_interstage_del_chain_0_2
    (
        .clk(clk),
        .rst_n(rst_n),
        .clk_en(clk_en),
        .in_word(add_tree_stage_1_q[2]),
        .in_word_val(),
        .in_word_del(add_tree_stage_1[2]), 
        .in_word_val_del()
    );
add_cell
    #(
    .ADD_ARITH_CFG(C_ADD_ARITH_CFG),
    .ADD_IN_CYC_LEN(C_ADD_FXP_IN_CYC_LEN),
    .ADD_OUT_CYC_LEN(C_ADD_FXP_OUT_CYC_LEN)
    )
    add_tree_add_cell_1_0
    ( 
      .clk(clk),
      .rst_n(rst_n),
      .clk_en(clk_en),
      .add_op_a(add_tree_stage_1[0]), 
      .add_op_b(add_tree_stage_1[1]),
      .add_op_val(),
      .add_res(add_tree_stage_2_q[0]),
      .add_res_val()
    );
del_chain
    #(
        .IN_WORD_WDT(C_ARITH_WORD_LEN),
        .DEL_CYC_LEN(C_ADD_TREE_LVL_DEL_CYC_LEN)
    )
    add_tree_interstage_del_chain_1_0
    (
        .clk(clk),
        .rst_n(rst_n),
        .clk_en(clk_en),
        .in_word(add_tree_stage_2_q[0]),
        .in_word_val(),
        .in_word_del(add_tree_stage_2[0]), 
        .in_word_val_del()
    );
del_chain
    #(
        .IN_WORD_WDT(C_ARITH_WORD_LEN),
        .DEL_CYC_LEN(C_ADD_FXP_CYC_LEN)
    )
    add_tree_del_chain_1_1
    (
        .clk(clk),
        .rst_n(rst_n),
        .clk_en(clk_en),
        .in_word(add_tree_stage_1[2]),
        .in_word_val(),
        .in_word_del(add_tree_stage_2_q[1]), 
        .in_word_val_del()
    );
del_chain
    #(
        .IN_WORD_WDT(C_ARITH_WORD_LEN),
        .DEL_CYC_LEN(C_ADD_TREE_LVL_DEL_CYC_LEN)
    )
    add_tree_interstage_del_chain_1_1
    (
        .clk(clk),
        .rst_n(rst_n),
        .clk_en(clk_en),
        .in_word(add_tree_stage_2_q[1]),
        .in_word_val(),
        .in_word_del(add_tree_stage_2[1]), 
        .in_word_val_del()
    );
add_cell
    #(
    .ADD_ARITH_CFG(C_ADD_ARITH_CFG),
    .ADD_IN_CYC_LEN(C_ADD_FXP_IN_CYC_LEN),
    .ADD_OUT_CYC_LEN(C_ADD_FXP_OUT_CYC_LEN)
    )
    add_tree_add_cell_2_0
    ( 
      .clk(clk),
      .rst_n(rst_n),
      .clk_en(clk_en),
      .add_op_a(add_tree_stage_2[0]), 
      .add_op_b(add_tree_stage_2[1]),
      .add_op_val(),
      .add_res(add_tree_stage_3_q[0]),
      .add_res_val()
    );
del_chain
    #(
        .IN_WORD_WDT(C_ARITH_WORD_LEN),
        .DEL_CYC_LEN(C_ADD_TREE_LVL_DEL_CYC_LEN)
    )
    add_tree_interstage_del_chain_2_0
    (
        .clk(clk),
        .rst_n(rst_n),
        .clk_en(clk_en),
        .in_word(add_tree_stage_3_q[0]),
        .in_word_val(),
        .in_word_del(add_tree_stage_3[0]), 
        .in_word_val_del()
    );
    assign add_tree_res =  add_tree_stage_3[0];
    endmodule
