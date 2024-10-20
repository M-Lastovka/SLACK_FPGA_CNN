`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     nlin_f_unit
// Project Name:    Efficient FPGA CNN implementation
// Description:     Block for non-linear functions. Supports only functions with static
//                  parameters, which are point-wise.
//                  Currently supported: identity, ReLu
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module nlin_f_unit
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    //control
    proc_pipe_ctrl_if.proc_block  nlin_f_pipe_ctrl_if,
    input  tens_trans_spec_t      nlin_f_tens_trans_spec,
    output tens_trans_spec_t      nlin_f_tens_trans_spec_i,
    //data & address 
    input  pipe_data_vect_t nlin_f_data_fetch,
    output pipe_data_vect_t nlin_f_data_out
);

//clock enables, resets
logic nlin_f_rst_n;
logic nlin_f_clk_en;

assign nlin_f_rst_n = !(!rst_n | nlin_f_pipe_ctrl_if.clear);
assign nlin_f_clk_en = nlin_f_pipe_ctrl_if.step;
assign nlin_f_pipe_ctrl_if.stall = !nlin_f_pipe_ctrl_if.step; //simply propagate

//-------------------------------------------------------------
//Inputs register----------------------------------------------
//-------------------------------------------------------------

pipe_data_vect_t nlin_f_data_fetch_del;
pipe_data_vect_t nlin_f_data_out_q;
pipe_data_vect_t nlin_f_data_id_res;
pipe_data_vect_t nlin_f_data_relu_res;
pipe_data_vect_t nlin_f_data_tanh_res;
pipe_data_t      nlin_f_data_tanh_ops[C_VECT_SIZE-1:0];
pipe_data_t      nlin_f_data_tanh_res_i[C_VECT_SIZE-1:0];


del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_NLIN_F_IN_DEL_CYC_LEN)
)
nlin_f_in_del_chain
(
    .clk(clk),
    .rst_n(nlin_f_rst_n),
    .clk_en(nlin_f_clk_en),
    .in_word(nlin_f_data_fetch),
    .in_word_val(),
    .in_word_del(nlin_f_data_fetch_del),
    .in_word_val_del()
);

always_ff @(posedge clk) begin : curr_acc_bmm_cnt_proc //keep count of the current number of bmm products
    if(!nlin_f_rst_n) begin
        nlin_f_tens_trans_spec_i <= '0;
    end else begin
        if(nlin_f_clk_en) begin
            nlin_f_tens_trans_spec_i <= nlin_f_tens_trans_spec;
        end
    end
end

//identity function
always_comb begin : nlin_f_id_proc
    if(nlin_f_tens_trans_spec_i.tens_trans_cfg.nlin_f_type == NLIN_F_IDENTITY & nlin_f_data_fetch_del.data_vect_type == TYPE_DATA & nlin_f_data_fetch_del.data_vect_val) begin
        nlin_f_data_id_res = nlin_f_data_fetch_del;
    end else begin
        nlin_f_data_id_res = C_PIPE_DATA_VECT_RST_VAL;
    end
end

//ReLu function
always_comb begin : nlin_f_relu_proc
    if(nlin_f_tens_trans_spec_i.tens_trans_cfg.nlin_f_type == NLIN_F_RELU & nlin_f_data_fetch_del.data_vect_type == TYPE_DATA & nlin_f_data_fetch_del.data_vect_val) begin
        foreach(nlin_f_data_fetch_del.data_vect_words[i])
            nlin_f_data_relu_res.data_vect_words[i] = $signed(nlin_f_data_fetch_del.data_vect_words[i]) >= 0 ? nlin_f_data_fetch_del.data_vect_words[i] : '0;
        nlin_f_data_relu_res.data_vect_val  = nlin_f_data_fetch_del.data_vect_val;
        nlin_f_data_relu_res.data_vect_last = nlin_f_data_fetch_del.data_vect_last;
        nlin_f_data_relu_res.data_vect_type = nlin_f_data_fetch_del.data_vect_type;
    end else begin
        nlin_f_data_relu_res = C_PIPE_DATA_VECT_RST_VAL;
    end
end

//Tanh function
always_comb begin : nlin_f_tanh_proc
    foreach(nlin_f_data_tanh_ops[i]) begin
        if(nlin_f_tens_trans_spec_i.tens_trans_cfg.nlin_f_type == NLIN_F_TANH & nlin_f_data_fetch_del.data_vect_type == TYPE_DATA & nlin_f_data_fetch_del.data_vect_val) begin
            nlin_f_data_tanh_ops[i].data_word      = nlin_f_data_fetch_del.data_vect_words[i];
            nlin_f_data_tanh_ops[i].data_val       = nlin_f_data_fetch_del.data_vect_val;
            nlin_f_data_tanh_ops[i].data_last      = nlin_f_data_fetch_del.data_vect_last;
            nlin_f_data_tanh_ops[i].data_type      = nlin_f_data_fetch_del.data_vect_type;
        end else begin
            nlin_f_data_tanh_ops[i].data_word      = C_PIPE_DATA_RST_VAL;
            nlin_f_data_tanh_ops[i].data_val       = 1'b0;
            nlin_f_data_tanh_ops[i].data_last      = 1'b0;
            nlin_f_data_tanh_ops[i].data_type      = '0;
        end
    end

    foreach(nlin_f_data_tanh_res.data_vect_words[i])
        nlin_f_data_tanh_res.data_vect_words[i] = nlin_f_data_tanh_res_i[i].data_word;
    nlin_f_data_tanh_res.data_vect_val  = nlin_f_data_tanh_res_i[0].data_val;
    nlin_f_data_tanh_res.data_vect_type = nlin_f_data_tanh_res_i[0].data_type;
    nlin_f_data_tanh_res.data_vect_last = nlin_f_data_tanh_res_i[0].data_last;
end

//output MUX
always_comb begin : nlin_f_mux
    casez (nlin_f_tens_trans_spec_i.tens_trans_cfg.nlin_f_type)
        NLIN_F_IDENTITY: nlin_f_data_out_q = nlin_f_data_id_res;
        NLIN_F_RELU:     nlin_f_data_out_q = nlin_f_data_relu_res;
        NLIN_F_TANH:     nlin_f_data_out_q = nlin_f_data_tanh_res;
        default:         nlin_f_data_out_q = C_PIPE_DATA_VECT_RST_VAL;
    endcase
end

genvar i;
generate
    for(i = 0; i < C_VECT_SIZE; i++) begin
        tanh_unit tanh_unit_inst
        (
            .clk(clk),
            .rst_n(nlin_f_rst_n),
            .clk_en(nlin_f_clk_en),
            .tanh_op(nlin_f_data_tanh_ops[i]),
            .tanh_res(nlin_f_data_tanh_res_i[i])
        );
    end
endgenerate

//-------------------------------------------------------------
//Outputs Registering------------------------------------------
//-------------------------------------------------------------

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_NLIN_F_OUT_DEL_CYC_LEN)
)
nlin_f_out_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(nlin_f_clk_en),
    .in_word(nlin_f_data_out_q),
    .in_word_val(),
    .in_word_del(nlin_f_data_out),
    .in_word_val_del()
);

// synthesis translate_off

//assertions

//only moving values are allowed inside non-linear function unit
always @(posedge clk) assert (!(nlin_f_data_fetch.data_vect_val & nlin_f_data_fetch.data_vect_type != TYPE_DATA) | !rst_n) else $error("Only moving values shall be routed to the activation function unit!");

// synthesis translate_on

endmodule