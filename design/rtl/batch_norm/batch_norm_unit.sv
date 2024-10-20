`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     batch_norm_unit
// Project Name:    Efficient FPGA CNN implementation
// Description:     Block for computing inference batch normalization. Batch normalization is 
//                  computed as x_bnorm_i = (x_i - mu_i)/(sqrt(sigma_i^2 + eps))*gamma_i + beta_i
//                  where i is the dimension index - channel index in case of conv.
//                  Since mu, sigma, eps, gamma and beta are all constants we reduce this transform
//                  to a single affine transformation, i.e. x_bnorm_i = scale_i*x_i + offset_i.
//
//                  For both the linear and conv layer the computation is applied the same here, i.e.
//                  we store a set of two vectors of the batch. norm. params: scale and offset 
//                  and then the operation is performed in a pipelined manner
//
//                  The batch. norm. params are stored in two registers and they shall be over-
//                  written if the batch norm is enabled and a new set of batch params shows
//                  up at the input. The transform is applied when a new data arrives and batch
//                  norm is enabled, otherwise it gets routed straight to the output 
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module batch_norm_unit
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    //control
    proc_pipe_ctrl_if.proc_block  batch_norm_pipe_ctrl_if,
    input  tens_trans_spec_t       batch_norm_tens_trans_spec,
    output tens_trans_spec_t       batch_norm_tens_trans_spec_i,
    //data & address 
    input  pipe_data_vect_t batch_norm_data_fetch,
    output pipe_data_vect_t batch_norm_data_out
);

//clock enables, resets
logic batch_norm_rst_n;
logic batch_norm_clk_en;

assign batch_norm_rst_n = !(!rst_n | batch_norm_pipe_ctrl_if.clear);
assign batch_norm_clk_en = batch_norm_pipe_ctrl_if.step;
assign batch_norm_pipe_ctrl_if.stall = !batch_norm_pipe_ctrl_if.step; //simply propagate

//-------------------------------------------------------------
//Inputs register----------------------------------------------
//-------------------------------------------------------------

pipe_data_vect_t batch_norm_data_fetch_del;
pipe_data_vect_t batch_norm_data_fetch_del_i;

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_BATCH_NORM_IN_DEL_CYC_LEN)
)
batch_norm_in_del_chain
(
    .clk(clk),
    .rst_n(batch_norm_rst_n),
    .clk_en(batch_norm_clk_en),
    .in_word(batch_norm_data_fetch),
    .in_word_val(),
    .in_word_del(batch_norm_data_fetch_del),
    .in_word_val_del()
);

del_chain //delay the input some more to ensure last computation was done before rewriting params
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_ADD_FXP_CYC_LEN + C_MULT_FXP_CYC_LEN)
)
batch_param_del_chain
(
    .clk(clk),
    .rst_n(batch_norm_rst_n),
    .clk_en(batch_norm_clk_en),
    .in_word(batch_norm_data_fetch_del),
    .in_word_val(),
    .in_word_del(batch_norm_data_fetch_del_i),
    .in_word_val_del()
);

//-------------------------------------------------------------
//Batch norm registers & comp. pipeline------------------------
//-------------------------------------------------------------

pipe_data_vect_t batch_norm_data_scale;
pipe_data_vect_t batch_norm_data_offset;
pipe_data_t      batch_norm_scale_ops_a[C_VECT_SIZE-1:0];
pipe_data_t      batch_norm_scale_ops_b[C_VECT_SIZE-1:0];
pipe_data_t      batch_norm_scale_res[C_VECT_SIZE-1:0];
pipe_data_t      batch_norm_offset_ops_a[C_VECT_SIZE-1:0];
pipe_data_t      batch_norm_offset_ops_b[C_VECT_SIZE-1:0];
pipe_data_t      batch_norm_offset_res[C_VECT_SIZE-1:0];
pipe_data_vect_t batch_norm_data_out_q;
logic            batch_norm_load_mux;

always_ff @(posedge clk) begin : batch_norm_param_reg //registers holding the batch norm params
    if(!batch_norm_rst_n) begin
        batch_norm_data_scale        <= C_PIPE_DATA_VECT_RST_VAL;
        batch_norm_data_offset       <= C_PIPE_DATA_VECT_RST_VAL;
        batch_norm_tens_trans_spec_i <= '0;
        batch_norm_load_mux          <= 1'b0;
    end else begin
        if(batch_norm_clk_en) begin
            if(batch_norm_tens_trans_spec.tens_trans_cfg.batch_norm_en) begin
                if(batch_norm_data_fetch_del_i.data_vect_type == TYPE_BATCH_NORM_PARAM & batch_norm_data_fetch_del_i.data_vect_val) begin
                    if(batch_norm_load_mux == 0) begin //first write scale, then offset
                        batch_norm_data_scale <= batch_norm_data_fetch_del_i;
                    end else if(batch_norm_load_mux == 1) begin
                        batch_norm_data_offset <= batch_norm_data_fetch_del_i;
                    end
                    batch_norm_load_mux <= batch_norm_load_mux + 1;
                end
            end
            batch_norm_tens_trans_spec_i <= batch_norm_tens_trans_spec; //sample and forward to the next block
        end
    end
end

//input and output MUX
always_comb begin : batch_norm_mux
    foreach(batch_norm_scale_ops_b[i]) begin
        if(batch_norm_data_fetch_del.data_vect_type == TYPE_DATA & batch_norm_data_fetch_del.data_vect_val & batch_norm_tens_trans_spec_i.tens_trans_cfg.batch_norm_en) begin //scale
            batch_norm_scale_ops_b[i].data_word      = batch_norm_data_fetch_del.data_vect_words[i];
            batch_norm_scale_ops_b[i].data_val       = batch_norm_data_fetch_del.data_vect_val;
            batch_norm_scale_ops_b[i].data_last      = batch_norm_data_fetch_del.data_vect_last;
            batch_norm_scale_ops_b[i].data_type      = batch_norm_data_fetch_del.data_vect_type;
            batch_norm_scale_ops_a[i].data_word      = batch_norm_data_scale.data_vect_words[i];
            batch_norm_scale_ops_a[i].data_val       = batch_norm_data_scale.data_vect_val;
            batch_norm_scale_ops_a[i].data_last      = batch_norm_data_scale.data_vect_last;
            batch_norm_scale_ops_a[i].data_type      = batch_norm_data_scale.data_vect_type;
        end else begin
            batch_norm_scale_ops_b[i] = C_PIPE_DATA_RST_VAL;
            batch_norm_scale_ops_a[i] = C_PIPE_DATA_RST_VAL;
        end

        if(batch_norm_scale_res[0].data_type == TYPE_DATA & batch_norm_scale_res[0].data_val) begin //offset
            batch_norm_offset_ops_b[i]                = batch_norm_scale_res[i];
            batch_norm_offset_ops_a[i].data_word      = batch_norm_data_offset.data_vect_words[i];
            batch_norm_offset_ops_a[i].data_val       = batch_norm_data_offset.data_vect_val;
            batch_norm_offset_ops_a[i].data_last      = batch_norm_data_offset.data_vect_last;
            batch_norm_offset_ops_a[i].data_type      = batch_norm_data_offset.data_vect_type;
        end else begin
            batch_norm_offset_ops_b[i] = C_PIPE_DATA_RST_VAL;
            batch_norm_offset_ops_a[i] = C_PIPE_DATA_RST_VAL;  
        end

        if(batch_norm_data_fetch_del.data_vect_type == TYPE_DATA & batch_norm_data_fetch_del.data_vect_val & !batch_norm_tens_trans_spec_i.tens_trans_cfg.batch_norm_en) begin //outputs
            batch_norm_data_out_q = batch_norm_data_fetch_del; //batch norm is not enabled, bypass
        end else if(batch_norm_offset_res[0].data_val & batch_norm_offset_res[0].data_type == TYPE_DATA) begin
            batch_norm_data_out_q.data_vect_words[i] = batch_norm_offset_res[i].data_word;
            batch_norm_data_out_q.data_vect_val      = batch_norm_offset_res[i].data_val;
            batch_norm_data_out_q.data_vect_last     = batch_norm_offset_res[i].data_last;
            batch_norm_data_out_q.data_vect_type     = batch_norm_offset_res[i].data_type;
        end else begin
            batch_norm_data_out_q = C_PIPE_DATA_VECT_RST_VAL;
        end
    end
end

genvar i;
generate
    for(i = 0; i < C_VECT_SIZE; i++) begin
        mult_wrapp //scaling multiplier
        #(
            .MULT_ARITH_CFG(C_MULT_ARITH_CFG),
            .MULT_IN_CYC_LEN(C_MULT_FXP_IN_CYC_LEN),
            .MULT_OUT_CYC_LEN(C_MULT_FXP_OUT_CYC_LEN)
        )
        sys_arr_cell_mult_inst
        (
            .clk(clk),
            .rst_n(batch_norm_rst_n),
            .clk_en(batch_norm_clk_en),
            .mult_op_a(batch_norm_scale_ops_a[i]),   
            .mult_op_b(batch_norm_scale_ops_b[i]),   
            .mult_res(batch_norm_scale_res[i])
        );

        add_wrapp //offset adder
        #(
            .ADD_ARITH_CFG(C_ADD_ARITH_CFG),
            .ADD_IN_CYC_LEN(C_ADD_FXP_IN_CYC_LEN),
            .ADD_OUT_CYC_LEN(C_ADD_FXP_OUT_CYC_LEN)
        )
        sys_arr_acc_vect_add
        (
            .clk(clk),
            .rst_n(batch_norm_rst_n),
            .clk_en(batch_norm_clk_en),
            .add_op_a(batch_norm_offset_ops_a[i]),   
            .add_op_b(batch_norm_offset_ops_b[i]),   
            .add_res(batch_norm_offset_res[i])
        );
    end
endgenerate

//-------------------------------------------------------------
//Outputs Registering------------------------------------------
//-------------------------------------------------------------

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_BATCH_NORM_OUT_DEL_CYC_LEN)
)
batch_norm_out_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(batch_norm_clk_en),
    .in_word(batch_norm_data_out_q),
    .in_word_val(),
    .in_word_del(batch_norm_data_out),
    .in_word_val_del()
);

// synthesis translate_off

//assertions

//only batch norm params or moving values are allowed inside accumulator
always @(posedge clk) assert (!(batch_norm_data_fetch.data_vect_val & batch_norm_data_fetch.data_vect_type != TYPE_BATCH_NORM_PARAM & batch_norm_data_fetch.data_vect_type != TYPE_DATA) | !rst_n) else $error("Only moving values and batch norm params shall be routed to the batch norm unit!");

//all side-channel info in shall be the same within a vector
always @(posedge clk) assert (side_ch_match_vect(batch_norm_offset_res) | !rst_n)  else $error("Side-channel info shall be the same within batch norm output!");

// synthesis translate_on

endmodule