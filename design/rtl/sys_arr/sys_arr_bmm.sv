`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     sys_arr_bmm
// Project Name:    Efficient FPGA CNN implementation
// Description:     Cell array (excluding accumulator) of the systolic aray for block matrix multiplication.
//                  On a high level, it computes Y = W*X, where W is a NxN matrix and X is a NxM matrix.
//
//                  Comprises of NxN array of cells, each of which holds a stationary value (W matrix)
//                  in a register and computes its product with the moving value and then forwards it to an
//                  adder tree. Data then comes out in a skewed order and is de-skewed in a triangular buffer
//                  and the de-skewed data is then sent to the accumulator.
//
//                  The array can be in three states:
//                      1. idle
//                      2. stationary values are being loaded, while the last moving values are being propagated loading
//                      3. moving values are propagated, while the last stationary values are being loaded
//                  Overlapping of stationary value loading and moving values propagation is done to ensure maximum
//                  resource utilization. 
//                  
//                  Data coming into and out of array comes packed into a vector where all the
//                  side-channel information shall be the same within a vector
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module sys_arr_bmm
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    //data & address 
    input  pipe_data_vect_t sys_arr_data_to_bmm,
    output pipe_data_vect_t sys_arr_data_bmm_out
);

//-------------------------------------------------------------
//Inputs register----------------------------------------------
//-------------------------------------------------------------

pipe_data_vect_t sys_arr_data_bmm_del;

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_SYS_ARR_IN_DEL_CYC_LEN)
)
sys_arr_in_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(sys_arr_data_to_bmm),
    .in_word_val(),
    .in_word_del(sys_arr_data_bmm_del),
    .in_word_val_del()
);

pipe_data_t sys_arr_cell_data[C_VECT_SIZE:0][C_VECT_SIZE-1:0];
pipe_data_t sys_arr_data_add_tree_ops[C_VECT_SIZE-1:0][C_VECT_SIZE-1:0];
pipe_data_t sys_arr_data_add_tree_res[C_VECT_SIZE-1:0];

always_comb begin
    for(int i = 0; i < C_VECT_SIZE; i++) begin
        sys_arr_cell_data[0][i].data_word      = sys_arr_data_bmm_del.data_vect_words[i];
        sys_arr_cell_data[0][i].data_val       = sys_arr_data_bmm_del.data_vect_val;
        sys_arr_cell_data[0][i].data_last      = sys_arr_data_bmm_del.data_vect_last;
        sys_arr_cell_data[0][i].data_type      =  sys_arr_data_bmm_del.data_vect_type;
    end
end

//-------------------------------------------------------------
//Cell array & triang. buffer----------------------------------
//-------------------------------------------------------------

genvar i,j;
generate
    for(i = 0; i < C_SYS_ARR_SIZE; i++) begin //column
        for(j = 0; j < C_SYS_ARR_SIZE; j++) begin //row
            sys_arr_cell
            #(
                .WEIGHT_STAT_CNT_MAX(C_SYS_ARR_SIZE-i-1)
            )
            sys_arr_cell_inst
            (
                .clk(clk),
                .rst_n(rst_n),
                .clk_en(clk_en),
                .sys_arr_data_l_cell(sys_arr_cell_data[i][j]), 
                .sys_arr_data_r_cell(sys_arr_cell_data[i+1][j]), 
                .sys_arr_data_add_tree(sys_arr_data_add_tree_ops[i][j])
            );
        end

        add_tree_wrapp sys_arr_add_tree_wrapp_inst
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .sys_arr_data_add_tree_ops(sys_arr_data_add_tree_ops[i]),
            .sys_arr_add_tree_res(sys_arr_data_add_tree_res[i])
        );

        del_chain //column buffer
        #(
            .IN_WORD_WDT(C_PIPE_DATA_WDT),
            .DEL_CYC_LEN(C_SYS_ARR_CELL_FORW_CYC_LEN*(C_VECT_SIZE-i-1))
        )
        tr_buff_del_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word(sys_arr_data_add_tree_res[i]),
            .in_word_val(),
            .in_word_del(sys_arr_data_to_acc_q[i]),
            .in_word_val_del()
        );
    end
endgenerate

//-------------------------------------------------------------
//Outputs MUXing and registering-------------------------------
//-------------------------------------------------------------

pipe_data_t      sys_arr_data_to_acc_q[C_VECT_SIZE-1:0];
pipe_data_vect_t sys_arr_data_to_acc_v_q;

always_comb begin
    foreach(sys_arr_data_to_acc_v_q.data_vect_words[i]) begin
        sys_arr_data_to_acc_v_q.data_vect_words[C_VECT_SIZE-1 - i] = sys_arr_data_to_acc_q[i].data_word;
        sys_arr_data_to_acc_v_q.data_vect_last = sys_arr_data_to_acc_q[i].data_last;
        sys_arr_data_to_acc_v_q.data_vect_val  = sys_arr_data_to_acc_q[i].data_val;
        sys_arr_data_to_acc_v_q.data_vect_type = sys_arr_data_to_acc_q[i].data_type;
    end
end

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_SYS_ARR_OUT_DEL_CYC_LEN)
)
sys_arr_out_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(sys_arr_data_to_acc_v_q),
    .in_word_val(),
    .in_word_del(sys_arr_data_bmm_out),
    .in_word_val_del()
);

// synthesis translate_off

//assertions

//all side-channel info in shall be the same within a vector
always @(posedge clk) assert (side_ch_match_vect(sys_arr_data_to_acc_q) | !rst_n)  else $error("Side-channel info shall be the same within the input vector!");
always @(posedge clk) assert (side_ch_match_vect(sys_arr_cell_data[0]) | !rst_n) else $error("Side-channel info shall be the same within the output vector!");

//after a vector with asserted last signal, data type shall change
assert property (@(posedge clk) disable iff (!rst_n) (sys_arr_data_to_bmm.data_vect_val & sys_arr_data_to_bmm.data_vect_last & clk_en|-> ##1 $changed(sys_arr_data_to_bmm.data_vect_type) | !sys_arr_data_to_bmm.data_vect_last)) else $error("After last signal is asserted, data type of input vector shall change!");

// synthesis translate_on

endmodule