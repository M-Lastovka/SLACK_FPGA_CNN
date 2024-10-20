`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     maxpool_unit
// Project Name:    Efficient FPGA CNN implementation
// Description:     Block for computing maxpooling. Vectors of a given window are 'accumulated'
//                  and then once all vectors of a given window have been processed, they are 
//                  sent to the output port. Data passes through unmodified if maxpooling is 
//                  not enabled. 
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module maxpool_unit
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    //control
    proc_pipe_ctrl_if.proc_block  maxpool_pipe_ctrl_if,
    input  tens_trans_spec_t      maxpool_tens_trans_spec,
    output tens_trans_spec_t      maxpool_tens_trans_spec_i,
    //data & address 
    input  pipe_data_vect_t maxpool_data_fetch,
    output pipe_data_vect_t maxpool_data_out
);

//clock enables, resets
logic maxpool_rst_n;
logic maxpool_clk_en;

assign maxpool_rst_n = !(!rst_n | maxpool_pipe_ctrl_if.clear);
assign maxpool_clk_en = maxpool_pipe_ctrl_if.step;
assign maxpool_pipe_ctrl_if.stall = !maxpool_pipe_ctrl_if.step; //simply propagate

//-------------------------------------------------------------
//Inputs register----------------------------------------------
//-------------------------------------------------------------

pipe_data_vect_t maxpool_data_fetch_del;

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_MAXPOOL_IN_DEL_CYC_LEN)
)
maxpool_in_del_chain
(
    .clk(clk),
    .rst_n(maxpool_rst_n),
    .clk_en(maxpool_clk_en),
    .in_word(maxpool_data_fetch),
    .in_word_val(),
    .in_word_del(maxpool_data_fetch_del),
    .in_word_val_del()
);

//-------------------------------------------------------------
//Maxpool accumulation-----------------------------------------
//-------------------------------------------------------------

//given a window of points of the feature map: [0, 2, 1, 7], [9, -9, 9, 0], [17, 4, 3, 0], [-1, 0, 3, -3]
//and a vector size 2, we will receive the vectors in this order: [0, 2], [1, 7], [9, -9], [9, 0], [17, 4], [3, 0], [-1, 0], [3, -3]
//we have an 'accumulator' memory which contains a single feature map point and stores the current maxima for all the dimensions
//example operation for the given vector stream:
//  |  old maxpool accumulator     |  input vector  |  new maxpool accumulator  |
//    [-inf, -inf, -inf, -inf]           [0, 2]        [0, 2, -inf, -inf]
//    [0, 2, -inf, -inf]                 [1, 7]        [0, 2, 1, 7]
//    [0, 2, 1, 7]                       [9, -9]       [9, 2, 1, 7]
//    [9, 2, 1, 7]                       [9, 0]        [9, 2, 9, 7]
//                                     ...........
//    [17, 4, 9, 7]                      [3, -3]       [17, 4, 9, 7]

//indicate the position of the current vector within a window
logic [C_TENS_DIM_WDT-1:0] maxpool_wind_pos_0;
logic [C_TENS_DIM_WDT-1:0] maxpool_wind_pos_1;
logic [C_TENS_DIM_WDT-1:0] maxpool_wind_pos_2;
logic maxpool_first_wind_point;
logic maxpool_last_wind_point;
logic maxpool_first_wind_point_q;
logic maxpool_last_wind_point_q;
pipe_data_vect_t maxpool_data;
pipe_data_vect_t maxpool_data_out_q;
logic [C_VECT_SIZE-1:0][C_ARITH_WORD_LEN-1:0] maxpool_acc_data_vect_words;
logic [C_VECT_SIZE-1:0][C_ARITH_WORD_LEN-1:0] maxpool_compar_res;
logic [C_VECT_SIZE-1:0][C_ARITH_WORD_LEN-1:0] maxpool_compar_res_i;
logic maxpool_acc_mem_rd_wr_coll;

//memory and interface instantiation
mem_if 
#(
    .RD_ADDR_WDT(C_MAXPOOL_ACC_ADDR_WDT),
    .DATA_OUT_WDT(C_VECT_WORD_WDT),
    .WR_ADDR_WDT(C_MAXPOOL_ACC_ADDR_WDT),
    .DATA_IN_WDT(C_VECT_WORD_WDT),
    .PIPE_IN_CNT(C_MAXPOOL_ACC_MEM_PIPE_IN_CNT),
    .PIPE_OUT_CNT(C_MAXPOOL_ACC_MEM_PIPE_OUT_CNT)
) maxpool_acc_mem_if(); 

always_ff @(posedge clk) begin : maxpool_wind_pos_reg //update the vector position
    if(!maxpool_rst_n) begin
        maxpool_wind_pos_0 <= '0;
        maxpool_wind_pos_1 <= '0;
        maxpool_wind_pos_2 <= '0;
        maxpool_tens_trans_spec_i <= '0;
    end else begin
        if(maxpool_clk_en) begin
            if(maxpool_tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_MAXPOOL) begin
                if(maxpool_data_fetch_del.data_vect_val) begin
                    if(maxpool_wind_pos_2 >= maxpool_tens_trans_spec_i.tens_trans_conv_dims.tens_src_b_dims.tens_2_dim-1) begin
                        maxpool_wind_pos_2 <= '0;
                        if(maxpool_wind_pos_1 >= maxpool_tens_trans_spec_i.tens_trans_conv_dims.tens_src_a_dims.tens_1_dim-1) begin
                            maxpool_wind_pos_1 <= '0;
                            if(maxpool_wind_pos_0 >= maxpool_tens_trans_spec_i.tens_trans_conv_dims.tens_src_a_dims.tens_0_dim-1) begin
                                maxpool_wind_pos_0 <= '0;
                            end else begin
                                maxpool_wind_pos_0 <= maxpool_wind_pos_0 + 1;
                            end
                        end else begin
                            maxpool_wind_pos_1 <= maxpool_wind_pos_1 + 1;
                        end
                    end else begin
                        maxpool_wind_pos_2 <= maxpool_wind_pos_2 + 1;
                    end
                end
            end
            maxpool_tens_trans_spec_i <= maxpool_tens_trans_spec;
        end
    end
end

always_comb begin : maxpool_acc_mem_rd_cmd //read command generation for the accumulator memory 
    maxpool_acc_mem_if.rd_en   = maxpool_clk_en & maxpool_data_fetch_del.data_vect_val & maxpool_tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_MAXPOOL;
    maxpool_acc_mem_if.rd_addr = maxpool_wind_pos_2;
end

always_comb begin : maxpool_wind_first_last_gen //generate flags indicating the first and last point within a window
    maxpool_first_wind_point_q = maxpool_wind_pos_0 == maxpool_wind_pos_1 & maxpool_wind_pos_0 == 0;
    maxpool_last_wind_point_q  = maxpool_wind_pos_0 == maxpool_tens_trans_spec_i.tens_trans_conv_dims.tens_src_a_dims.tens_0_dim-1 & maxpool_wind_pos_1 == maxpool_tens_trans_spec_i.tens_trans_conv_dims.tens_src_a_dims.tens_1_dim-1;
end

//delay the data while the accumulator data is being fetched
del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_MAXPOOL_ACC_FETCH_CYC_LEN)
)
maxpool_acc_vect_del_chain
(
    .clk(clk),
    .rst_n(maxpool_rst_n),
    .clk_en(maxpool_clk_en),
    .in_word(maxpool_data_fetch_del),
    .in_word_val(),
    .in_word_del(maxpool_data),
    .in_word_val_del()
);

//delay the first point flag
del_chain
#(
    .IN_WORD_WDT(1),
    .DEL_CYC_LEN(C_MAXPOOL_ACC_FETCH_CYC_LEN)
)
maxpool_first_point_del_chain
(
    .clk(clk),
    .rst_n(maxpool_rst_n),
    .clk_en(maxpool_clk_en),
    .in_word(maxpool_first_wind_point_q),
    .in_word_val(),
    .in_word_del(maxpool_first_wind_point),
    .in_word_val_del()
);

//delay the last point flag
del_chain
#(
    .IN_WORD_WDT(1),
    .DEL_CYC_LEN(C_MAXPOOL_ACC_COMP_CYC_LEN)
)
maxpool_last_point_del_chain
(
    .clk(clk),
    .rst_n(maxpool_rst_n),
    .clk_en(maxpool_clk_en),
    .in_word(maxpool_last_wind_point_q),
    .in_word_val(),
    .in_word_del(maxpool_last_wind_point),
    .in_word_val_del()
);

//delay input vector before the accumulator is read
del_chain
#(
    .IN_WORD_WDT(C_MAXPOOL_ACC_ADDR_WDT),
    .DEL_CYC_LEN(C_MAXPOOL_ACC_COMP_CYC_LEN)
)
maxpool_acc_wr_del_chain
(
    .clk(clk),
    .rst_n(maxpool_rst_n),
    .clk_en(maxpool_clk_en),
    .in_word(maxpool_acc_mem_if.rd_addr),
    .in_word_val(maxpool_acc_mem_if.rd_en),
    .in_word_del(maxpool_acc_mem_if.wr_addr),
    .in_word_val_del(maxpool_acc_mem_if.wr_en)
);

gen_mem_simple_dual maxpool_acc_mem //accumulator memory
(
    .clk(clk),
    .clk_wr_en(maxpool_clk_en),
    .clk_rd_en(maxpool_clk_en),
    .rst_n(maxpool_rst_n),
    .gen_mem_if(maxpool_acc_mem_if)
);

always_ff @(posedge clk) begin : maxpool_compar_res_reg //keep the comparison result in a register if read and write collision occurs
    if(!maxpool_rst_n) begin
        maxpool_compar_res_i       <= '0;
        maxpool_acc_mem_rd_wr_coll <= 1'b0;
    end else begin
        if(maxpool_clk_en) begin
            maxpool_compar_res_i <= maxpool_compar_res;
            maxpool_acc_mem_rd_wr_coll <= maxpool_acc_mem_if.wr_addr == maxpool_acc_mem_if.rd_addr & maxpool_acc_mem_if.wr_en & maxpool_acc_mem_if.rd_en;
        end
    end
end

//comparison
always_comb begin
    foreach(maxpool_data.data_vect_words[i]) begin
        if(maxpool_acc_mem_rd_wr_coll) //handle the case if the acc memory is not write first
            maxpool_acc_data_vect_words[i] = maxpool_compar_res_i[i];
        else
            maxpool_acc_data_vect_words[i] = maxpool_acc_mem_if.data_out[i*C_ARITH_WORD_LEN +: C_ARITH_WORD_LEN];

        if(maxpool_first_wind_point | $signed(maxpool_data.data_vect_words[i]) > $signed(maxpool_acc_data_vect_words[i]))
            maxpool_compar_res[i] = maxpool_data.data_vect_words[i];
        else 
            maxpool_compar_res[i] = maxpool_acc_data_vect_words[i];
        
        maxpool_acc_mem_if.data_in[i*C_ARITH_WORD_LEN +: C_ARITH_WORD_LEN] = maxpool_compar_res[i];
    end
end

//output MUX
always_comb begin : maxpool_out_mux
    if(maxpool_tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_MAXPOOL) begin
        if(maxpool_last_wind_point) begin
            foreach(maxpool_data_out_q.data_vect_words[i]) begin
                maxpool_data_out_q.data_vect_words[i] = maxpool_compar_res[i];
                maxpool_data_out_q.data_vect_type     = maxpool_data.data_vect_type;
                maxpool_data_out_q.data_vect_val      = maxpool_data.data_vect_val;
                maxpool_data_out_q.data_vect_last     = maxpool_data.data_vect_last;
            end
        end else begin
            maxpool_data_out_q = C_PIPE_DATA_VECT_RST_VAL;
        end
    end else begin
        maxpool_data_out_q = maxpool_data_fetch_del;
    end
end

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_MAXPOOL_OUT_DEL_CYC_LEN)
)
maxpool_out_del_chain
(
    .clk(clk),
    .rst_n(maxpool_rst_n),
    .clk_en(maxpool_clk_en),
    .in_word(maxpool_data_out_q),
    .in_word_val(),
    .in_word_del(maxpool_data_out),
    .in_word_val_del()
);

// synthesis translate_off

//assertions

//only moving values are allowed inside maxpool unit
always @(posedge clk) assert (!(maxpool_data_fetch.data_vect_val & maxpool_data_fetch.data_vect_type != TYPE_DATA) | !maxpool_rst_n) else $error("Only moving values and batch norm params shall be routed to the batch norm unit!");
// synthesis translate_on

endmodule