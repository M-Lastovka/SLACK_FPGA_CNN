`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     sys_arr
// Project Name:    Efficient FPGA CNN implementation
// Description:     Systolic array for high-efficiency, high throughput matrix multiplication.
//                  Constists of a cell array, adder trees and triangular buffer (sys_arr_bmm.sv)
//                  which do block level matrix multiplication. The results are accumualted 
//                  and saved in the accumulator block (sys_arr_acc.sv).
//                  Example: given matrices A (8x8) and B (8x12) and vector width 4 (=array size)
//                  we partition the matrices A = | A_11 A_12 | B = | B_11 |
//                                                | A_21 A_22 |     | B_21 |
//                  and then always load A_ij as the stationary value to the BMM block and the 
//                  B as the moving value and then accumulate: ((A_11*B_11) + A_12*B_21) = R_11
//                  and after that R_21 is computed and so on.
//
//                  We can also utilize load the accumulator with a bias C
//                  to allow computation: A*B + C = D. If the replicate bias flag is set, the
//                  single bias vector column is replicated across all columns
//
//                  Batch norm. params will be passed through the sys.arr.
//
//                  All relevant metadata is passed to the sys.arr. by the sys_arr_tens_trans_spec
//                  and sys_arr_tens_trans_dims structures and the processing is started by the 
//                  address generation unit through the sys_arr_ctrl_if interface
// 
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module sys_arr
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    //control
    block_ctrl_if.slave           sys_arr_ctrl_if,
    proc_pipe_ctrl_if.proc_block  sys_arr_pipe_ctrl_if,
    input  tens_trans_spec_t      sys_arr_tens_trans_spec,
    output tens_trans_spec_t      sys_arr_tens_trans_spec_i,
    input  mtx_trans_dims_t       sys_arr_tens_trans_lin_dims,
    //data & address 
    input  pipe_data_vect_t sys_arr_data_fetch,
    output pipe_data_vect_t sys_arr_data_out
);

typedef enum 
{
    IDLE,
    COMP,
    STALL,
    N_COMP
} 
sys_arr_state_t;

sys_arr_state_t sys_arr_curr_state;
sys_arr_state_t sys_arr_next_state;

//clock enables, resets
logic sys_arr_rst_n_q;
logic sys_arr_rst_n = 1'b1;
logic sys_arr_clk_en;
logic sys_arr_in_clk_en;
logic sys_arr_in_step;

assign sys_arr_rst_n_q = !(!rst_n | sys_arr_pipe_ctrl_if.clear);
assign sys_arr_clk_en = sys_arr_pipe_ctrl_if.step;
assign sys_arr_pipe_ctrl_if.stall = !sys_arr_pipe_ctrl_if.step | !sys_arr_in_step; //propagate + stall of input
assign sys_arr_ctrl_if.done  = 1'b0; //do not return a done signal 
assign sys_arr_in_clk_en = sys_arr_clk_en & sys_arr_in_step; 

always_ff @(posedge clk) begin : sys_arr_rst_gen_reg
    sys_arr_rst_n <= sys_arr_rst_n_q;
end

//register holding the state of the sys. arr., either we are computing or loading/forwarding data
always_ff @(posedge clk) begin : sys_arr_state
    if(!sys_arr_rst_n) begin
        sys_arr_curr_state <= IDLE; 
    end else begin
        if(sys_arr_clk_en) begin
            sys_arr_curr_state <= sys_arr_next_state;
        end
    end
end

always_comb begin : sys_arr_next_state_proc
    sys_arr_next_state = sys_arr_curr_state;
    casez (sys_arr_curr_state)
        IDLE   : 
            if(sys_arr_ctrl_if.start)
                if(sys_arr_tens_trans_spec.tens_trans_cfg.bias_en | sys_arr_tens_trans_spec.tens_trans_cfg.batch_norm_en) 
                    sys_arr_next_state = N_COMP;
                else 
                    sys_arr_next_state = COMP;
            else
                sys_arr_next_state = IDLE;
        N_COMP :
            if(sys_arr_data_fetch_del.data_vect_val & data_type_mov_or_stat(sys_arr_data_fetch_del.data_vect_type))
                sys_arr_next_state = COMP;
            else  
                sys_arr_next_state = N_COMP;
        COMP   :
            if(sys_arr_data_fetch_del.data_vect_val & !data_type_mov_or_stat(sys_arr_data_fetch_del.data_vect_type))
                sys_arr_next_state = STALL;
            else if(sys_arr_data_acc_out.data_vect_val & sys_arr_data_acc_out.data_vect_type == TYPE_DATA & sys_arr_data_acc_out.data_vect_last)
                sys_arr_next_state = N_COMP;
            else 
                sys_arr_next_state = COMP;
        STALL  : 
            if(sys_arr_data_acc_out.data_vect_val & sys_arr_data_acc_out.data_vect_type == TYPE_DATA & sys_arr_data_acc_out.data_vect_last)
                sys_arr_next_state = N_COMP;
            else 
                sys_arr_next_state = STALL;
    endcase
end

assign sys_arr_in_step = sys_arr_next_state != STALL & sys_arr_curr_state != STALL;

//-------------------------------------------------------------
//Inputs register----------------------------------------------
//-------------------------------------------------------------

pipe_data_vect_t sys_arr_data_fetch_del;

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_SYS_ARR_IN_DEL_CYC_LEN)
)
sys_arr_in_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(sys_arr_in_clk_en),
    .in_word(sys_arr_data_fetch),
    .in_word_val(),
    .in_word_del(sys_arr_data_fetch_del),
    .in_word_val_del()
);

//-------------------------------------------------------------
//BMM module---------------------------------------------------
//-------------------------------------------------------------

pipe_data_vect_t sys_arr_data_to_bmm;
pipe_data_vect_t sys_arr_data_bmm_out;

//input MUX - route only stationary or moving values
always_comb begin : sys_arr_bmm_in_mux
    if(data_type_mov_or_stat(sys_arr_data_fetch_del.data_vect_type) & sys_arr_data_fetch_del.data_vect_val & sys_arr_tens_trans_spec_i.tens_trans_cfg.tens_trans_type != TRANS_MAXPOOL)
        sys_arr_data_to_bmm = sys_arr_data_fetch_del;
    else
        sys_arr_data_to_bmm = C_PIPE_DATA_VECT_RST_VAL;
end

sys_arr_bmm sys_arr_bmm_inst
(
    .clk(clk),
    .rst_n(sys_arr_rst_n),
    .clk_en(sys_arr_clk_en),
    .sys_arr_data_to_bmm(sys_arr_data_to_bmm),
    .sys_arr_data_bmm_out(sys_arr_data_bmm_out)
);

//-------------------------------------------------------------
//Accumulator--------------------------------------------------
//-------------------------------------------------------------

pipe_data_vect_t sys_arr_data_to_acc;
pipe_data_vect_t sys_arr_data_acc_out;
logic repl_bias;
logic bias_en;
logic [C_TENS_DIM_WDT-1:0] acc_bmm_cnt_limit;

always_ff @(posedge clk) begin : sys_arr_acc_ctrl_reg //register holding the control info for accumulator, sampled on start signal
    if(!rst_n) begin
        repl_bias                <= 1'b0;
        bias_en                  <= 1'b0;
        acc_bmm_cnt_limit        <= '0;
        sys_arr_tens_trans_spec_i <= '0;
    end else begin
        if(sys_arr_clk_en) begin
            if(sys_arr_ctrl_if.start) begin 
                repl_bias                 <= sys_arr_tens_trans_spec.tens_trans_cfg.repl_bias;
                bias_en                   <= sys_arr_tens_trans_spec.tens_trans_cfg.bias_en;
                acc_bmm_cnt_limit         <= sys_arr_tens_trans_lin_dims.tens_src_a_dims.tens_1_dim; 
                sys_arr_tens_trans_spec_i <= sys_arr_tens_trans_spec; //sample and forward to the next block
            end
        end
    end
end

//input MUX - route only bias or data from the BMM module
always_comb begin : sys_arr_acc_in_mux
    if(sys_arr_data_fetch_del.data_vect_type == TYPE_ACC_BIAS & sys_arr_data_fetch_del.data_vect_val & sys_arr_tens_trans_spec_i.tens_trans_cfg.tens_trans_type != TRANS_MAXPOOL)
        sys_arr_data_to_acc = sys_arr_data_fetch_del;
    else if(sys_arr_data_bmm_out.data_vect_type == TYPE_DATA & sys_arr_data_bmm_out.data_vect_val & sys_arr_tens_trans_spec_i.tens_trans_cfg.tens_trans_type != TRANS_MAXPOOL)
        sys_arr_data_to_acc = sys_arr_data_bmm_out;
    else
        sys_arr_data_to_acc = C_PIPE_DATA_VECT_RST_VAL;
end

sys_arr_acc sys_arr_acc_inst
(
    .clk(clk),
    .rst_n(sys_arr_rst_n),
    .clk_en(sys_arr_clk_en),
    .repl_bias(repl_bias),
    .bias_en(bias_en),
    .acc_bmm_cnt_limit(acc_bmm_cnt_limit),
    .sys_arr_data_to_acc(sys_arr_data_to_acc),
    .sys_arr_data_acc_out(sys_arr_data_acc_out)
);

//-------------------------------------------------------------
//Outputs MUXing and registering-------------------------------
//-------------------------------------------------------------

pipe_data_vect_t sys_arr_data_out_q;

//output MUX - route accumulator output or batch.norm.params or maxpool data
always_comb begin : sys_arr_out_mux
    if((sys_arr_data_fetch_del.data_vect_type == TYPE_BATCH_NORM_PARAM | sys_arr_tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_MAXPOOL) & sys_arr_data_fetch_del.data_vect_val & sys_arr_in_step)
        sys_arr_data_out_q = sys_arr_data_fetch_del;
    else if(sys_arr_data_acc_out.data_vect_type == TYPE_DATA & sys_arr_data_acc_out.data_vect_val)
        sys_arr_data_out_q = sys_arr_data_acc_out;
    else
        sys_arr_data_out_q = C_PIPE_DATA_VECT_RST_VAL;
end

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_SYS_ARR_OUT_DEL_CYC_LEN)
)
sys_arr_out_del_chain
(
    .clk(clk),
    .rst_n(sys_arr_rst_n),
    .clk_en(sys_arr_clk_en),
    .in_word(sys_arr_data_out_q),
    .in_word_val(),
    .in_word_del(sys_arr_data_out),
    .in_word_val_del()
);

// synthesis translate_off

//assertions

//either we are forwarding bias or bmm output to the accumulator
always @(posedge clk) assert (!((sys_arr_data_fetch_del.data_vect_type == TYPE_ACC_BIAS & sys_arr_data_fetch_del.data_vect_val) & 
    (sys_arr_data_to_acc.data_vect_type == TYPE_DATA & sys_arr_data_to_acc.data_vect_val)) | !sys_arr_rst_n) else $error("Conflict at the input port of sys.arr. accumulator!");

//either we are forwarding batch.norm.params to the output port or sys.arr. outputs
always @(posedge clk) assert (!((sys_arr_data_fetch_del.data_vect_type == TYPE_BATCH_NORM_PARAM & sys_arr_data_fetch_del.data_vect_val) & 
    (sys_arr_data_acc_out.data_vect_type == TYPE_DATA & sys_arr_data_acc_out.data_vect_val)) | !sys_arr_in_clk_en | !sys_arr_rst_n) else $error("Conflict at the output port of sys.arr.!");

// synthesis translate_on

endmodule