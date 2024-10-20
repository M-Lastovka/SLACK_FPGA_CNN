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
//                  The cell can be in three states:
//                      1. idle
//                      2. stationary value loading
//                      3. data compuation
//                  When the stationary values are being loaded a counter is incremented each time
//                  a weight passes through the cell, once the counter is at max value, the
//                  stationary value has reached its destination cell and can be written to reg
//                  The counter shall be reset by the last moving data value once the stationary
//                  values become stale
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module sys_arr_cell
#(
    parameter WEIGHT_STAT_CNT_MAX = 0
)
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    //data & address 
    input  pipe_data_t sys_arr_data_l_cell,   //data from left cell
    output pipe_data_t sys_arr_data_r_cell,   //data to right cell
    output pipe_data_t sys_arr_data_add_tree  //multiplication product to adder tree
);

pipe_data_t stat_data;
pipe_data_t sys_arr_data_r_cell_q;
logic [C_VECT_SIZE_CLOG2-1:0] stat_data_load_cnt;
pipe_data_t [1:0] sys_arr_data_mult_ops;
pipe_data_t [1:0] sys_arr_data_mult_ops_del;

always_ff @(posedge clk) begin : stat_data_reg //stationary value register
    if(!rst_n) begin
        stat_data           <= C_PIPE_DATA_RST_VAL;
        stat_data_load_cnt  <= '0;
    end else begin
        if(clk_en) begin
            if(sys_arr_data_l_cell.data_type == TYPE_DATA & sys_arr_data_l_cell.data_val & sys_arr_data_l_cell.data_last) begin
                stat_data_load_cnt  <= '0;
                stat_data           <= C_PIPE_DATA_RST_VAL;
            end else if(sys_arr_data_l_cell.data_val & sys_arr_data_l_cell.data_type == TYPE_STAT_WEIGHT) begin
                if(stat_data_load_cnt == WEIGHT_STAT_CNT_MAX) begin
                    stat_data           <= sys_arr_data_l_cell; //stationary value has reached its final value, write to register
                end else begin
                    stat_data_load_cnt  <= stat_data_load_cnt + 1; //stationary value passed through the cell
                end
            end
        end
    end
end

//input to the forwarding delay chain - forward always in case of data input, stationary values only if the counter has not reached max value
assign sys_arr_data_r_cell_q = (sys_arr_data_l_cell.data_val & ((sys_arr_data_l_cell.data_type == TYPE_STAT_WEIGHT & stat_data_load_cnt != WEIGHT_STAT_CNT_MAX) | sys_arr_data_l_cell.data_type == TYPE_DATA) ) ?
    sys_arr_data_l_cell : C_PIPE_DATA_RST_VAL;

del_chain //forwading delay chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_WDT),
    .DEL_CYC_LEN(C_SYS_ARR_CELL_FORW_CYC_LEN)
)
sys_arr_cell_forw_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(sys_arr_data_r_cell_q),
    .in_word_val(),
    .in_word_del(sys_arr_data_r_cell),
    .in_word_val_del()
);

always_comb begin : mult_delay_chain_mux
    //asign stationary data and data from the left cell as mult inputs if they are valid and of correct type, else propagate zeros
    sys_arr_data_mult_ops[0] = stat_data.data_val ? stat_data : C_PIPE_DATA_VECT_RST_VAL; 
    sys_arr_data_mult_ops[1] = sys_arr_data_l_cell.data_val & sys_arr_data_l_cell.data_type == TYPE_DATA ? sys_arr_data_l_cell : C_PIPE_DATA_VECT_RST_VAL;
end

del_chain //delay chain to the multiplier inputs
#(
    .IN_WORD_WDT(2*C_PIPE_DATA_WDT),
    .DEL_CYC_LEN(C_SYS_ARR_CELL_MULT_CYC_LEN)
)
sys_arr_cell_mult_ops_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(sys_arr_data_mult_ops),
    .in_word_val(),
    .in_word_del(sys_arr_data_mult_ops_del),
    .in_word_val_del()
);

mult_wrapp //multiplier for computing product of moving and stationary value and moving value
#(
    .MULT_ARITH_CFG(C_MULT_ARITH_CFG),
    .MULT_IN_CYC_LEN(C_MULT_FXP_IN_CYC_LEN),
    .MULT_OUT_CYC_LEN(C_MULT_FXP_OUT_CYC_LEN)
)
sys_arr_cell_mult_inst
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .mult_op_a(sys_arr_data_mult_ops_del[0]),   
    .mult_op_b(sys_arr_data_mult_ops_del[1]),   
    .mult_res(sys_arr_data_add_tree)
);

// synthesis translate_off

//assertions

//only stationary data and moving data shall be propageted
always @(posedge clk) assert (data_type_mov_or_stat(sys_arr_data_l_cell.data_type) | !rst_n) else $error("Error in column: %d, only stationary data and moving data shall be propageted!", C_SYS_ARR_SIZE - WEIGHT_STAT_CNT_MAX - 1);

//once counter reaches maximum value, stationary weight shall be written and not change
assert property (@(posedge clk) disable iff (!rst_n) ((stat_data_load_cnt == WEIGHT_STAT_CNT_MAX & clk_en & 
    sys_arr_data_l_cell.data_type == TYPE_STAT_WEIGHT) |-> ##1 $changed(stat_data))) else $error("Error in column: %d, counter has reached max value but weight value has not changed!", C_SYS_ARR_SIZE - WEIGHT_STAT_CNT_MAX - 1);

//valid moving value from the left cell shall be always propagated
//assert property (@(posedge clk) disable iff (!rst_n) (sys_arr_data_l_cell.data_type == TYPE_DATA & sys_arr_data_l_cell.data_val & clk_en|-> ##2 sys_arr_data_r_cell == $past(sys_arr_data_l_cell, 2))) else $error("Error in column: %d, the valid moving value coming from left cell shall be propagated: %d!", C_SYS_ARR_SIZE - WEIGHT_STAT_CNT_MAX - 1, sys_arr_data_r_cell);

// synthesis translate_on

endmodule