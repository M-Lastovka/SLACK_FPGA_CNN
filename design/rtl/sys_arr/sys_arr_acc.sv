`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     sys_arr_acc
// Project Name:    Efficient FPGA CNN implementation
// Description:     Accumulator for the systolic array, consists of a vector adder and a memory.
//
//                  Functionally, it computes A + B = C, where A, B, C are matrices of size NxL,
//                  where N is the vector size and L is the maximum accumulator column count.
//                  A comes from the BMM module, B is read from the memory and C is then over-
//                  writing it.
//
//                  Bias may be loaded to the memory at the beginning and replicated column-wise
//                  if appropriate flag is set.
//                  
//                  When the last block matrix is being accumulated the results are directly
//                  routed to the accumulator output port
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;
import mem_pckg::*;

module sys_arr_acc
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    //control
    input logic  repl_bias,
    input logic  bias_en,
    input logic  [C_TENS_DIM_WDT-1:0] acc_bmm_cnt_limit,
    //data & address 
    input  pipe_data_vect_t sys_arr_data_to_acc,
    output pipe_data_vect_t sys_arr_data_acc_out
);

pipe_data_vect_t sys_arr_data_acc_del;
logic sys_arr_acc_bmm_first; //the first block matrix mult., use the replicated bias
logic sys_arr_acc_bmm_first_del;
logic sys_arr_acc_bmm_last;  //the last block matrix mult., route to output port, reset counters
logic sys_arr_acc_bmm_last_del; 

//delay to allow fetching of accumulated value
del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .DEL_CYC_LEN(C_SYS_ARR_ACC_FETCH_CYC_LEN)
)
sys_arr_in_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(sys_arr_data_to_acc),
    .in_word_val(sys_arr_acc_bmm_first),
    .in_word_del(sys_arr_data_acc_del),
    .in_word_val_del(sys_arr_acc_bmm_first_del)
);

//memory and interface instantiation
mem_if 
#(
    .RD_ADDR_WDT(C_SYS_ARR_ACC_ADDR_WDT),
    .DATA_OUT_WDT(C_VECT_WORD_WDT),
    .WR_ADDR_WDT(C_SYS_ARR_ACC_ADDR_WDT),
    .DATA_IN_WDT(C_VECT_WORD_WDT),
    .PIPE_IN_CNT(C_SYS_ARR_ACC_MEM_PIPE_IN_CNT),
    .PIPE_OUT_CNT(C_SYS_ARR_ACC_MEM_PIPE_OUT_CNT)
) sys_arr_acc_mem_if (); 

//-------------------------------------------------------------
//Accumulator memory access & ctrl-----------------------------
//-------------------------------------------------------------

logic [C_TENS_DIM_WDT-1:0] curr_acc_bmm_cnt; //counter the number of block matrix products accumulated

//issue read when valid data is coming, either non-replicated bias or moving data, which requires a memory read
assign sys_arr_acc_mem_if.rd_en = clk_en & sys_arr_data_to_acc.data_vect_val & 
    (sys_arr_data_to_acc.data_vect_type == TYPE_ACC_BIAS & !repl_bias & bias_en | 
    sys_arr_data_to_acc.data_vect_type == TYPE_DATA); 

always_ff @(posedge clk) begin : sys_arr_acc_mem_ctrl_gen //generate read control
    if(!rst_n) begin
        sys_arr_acc_mem_if.rd_addr <= '0;
    end else begin
        if(clk_en) begin
            if(sys_arr_acc_mem_if.rd_en & !sys_arr_data_to_acc.data_vect_last) //new valid vector coming, increment read address
                sys_arr_acc_mem_if.rd_addr <= sys_arr_acc_mem_if.rd_addr + 1;
            else if(sys_arr_acc_mem_if.rd_en & sys_arr_data_to_acc.data_vect_last) //new valid last vector coming, reset read address
                sys_arr_acc_mem_if.rd_addr <= '0;
        end
    end
end

always_ff @(posedge clk) begin : curr_acc_bmm_cnt_proc //keep count of the current number of bmm products
    if(!rst_n) begin
        curr_acc_bmm_cnt <= '0;
    end else begin
        if(clk_en) begin
            if(sys_arr_acc_mem_if.rd_en & sys_arr_data_to_acc.data_vect_last & sys_arr_data_to_acc.data_vect_type == TYPE_DATA) //moving value vector stream ended
                if(curr_acc_bmm_cnt < acc_bmm_cnt_limit-1)
                    curr_acc_bmm_cnt <= curr_acc_bmm_cnt + 1;
                else
                    curr_acc_bmm_cnt <= '0; //last bmm product, reset counter
        end
    end
end

assign sys_arr_acc_bmm_first = curr_acc_bmm_cnt == '0;
assign sys_arr_acc_bmm_last  = curr_acc_bmm_cnt == acc_bmm_cnt_limit-1;

//delayed last signal
del_chain
#(
    .IN_WORD_WDT(1),
    .DEL_CYC_LEN(C_SYS_ARR_ACC_ADD_CYC_LEN + C_SYS_ARR_ACC_FETCH_CYC_LEN)
)
sys_arr_acc_last_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(sys_arr_acc_bmm_last),
    .in_word_val(),
    .in_word_del(sys_arr_acc_bmm_last_del),
    .in_word_val_del()
);

//write access is only delayed read access
del_chain
#(
    .IN_WORD_WDT(C_SYS_ARR_ACC_ADDR_WDT),
    .DEL_CYC_LEN(C_SYS_ARR_ACC_ADD_CYC_LEN + C_SYS_ARR_ACC_FETCH_CYC_LEN)
)
sys_arr_acc_wr_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(sys_arr_acc_mem_if.rd_addr),
    .in_word_val(sys_arr_acc_mem_if.rd_en),
    .in_word_del(sys_arr_acc_mem_if.wr_addr),
    .in_word_val_del(sys_arr_acc_mem_if.wr_en)
);

bram_simple_dual sys_arr_acc_mem
(
    .clk(clk),
    .clk_wr_en(clk_en),
    .clk_rd_en(clk_en),
    .rst_n(rst_n),
    .bram_mem_if(sys_arr_acc_mem_if)
);

//-------------------------------------------------------------
//Accumulator vector adder & output muxing and registering-----
//-------------------------------------------------------------

pipe_data_vect_t sys_arr_acc_bias_repl;
pipe_data_t      sys_arr_acc_add_ops_a[C_VECT_SIZE-1:0];
pipe_data_t      sys_arr_acc_add_ops_b[C_VECT_SIZE-1:0];
pipe_data_t      sys_arr_acc_add_res[C_VECT_SIZE-1:0];

always_ff @(posedge clk) begin : bias_repl_reg //register holding the replicated bias, invalidate after the first bmm product
    if(!rst_n) begin
        sys_arr_acc_bias_repl <= C_PIPE_DATA_RST_VAL;
    end else begin
        if(clk_en) begin
            if(sys_arr_acc_bmm_first_del) begin
                if(sys_arr_data_acc_del.data_vect_type == TYPE_ACC_BIAS & sys_arr_data_acc_del.data_vect_last & sys_arr_data_acc_del.data_vect_val & repl_bias & bias_en) begin
                    sys_arr_acc_bias_repl <= sys_arr_data_acc_del;
                end
            end else begin
                sys_arr_acc_bias_repl <= C_PIPE_DATA_RST_VAL;
            end
        end
    end
end

//MUXing of the operators A, B of the vector adder, either we use the replicaated bias reg
// or the read output of the accumulator memory
//MUXing of the adder result
always_comb begin : sys_arr_vect_add_mux 
        foreach(sys_arr_acc_add_ops_b[i]) begin //input operands
            if(sys_arr_data_acc_del.data_vect_type == TYPE_DATA & sys_arr_data_acc_del.data_vect_val) begin
                sys_arr_acc_add_ops_b[i].data_word      = sys_arr_data_acc_del.data_vect_words[i];
                sys_arr_acc_add_ops_b[i].data_val       = sys_arr_data_acc_del.data_vect_val;
                sys_arr_acc_add_ops_b[i].data_last      = sys_arr_data_acc_del.data_vect_last;
                sys_arr_acc_add_ops_b[i].data_type      = sys_arr_data_acc_del.data_vect_type;
                if(sys_arr_acc_bmm_first_del & !bias_en) begin //bias is disabled, first bmm product, A = 0
                    sys_arr_acc_add_ops_a[i].data_word      = '0;
                    sys_arr_acc_add_ops_a[i].data_val       =  1'b1;
                    sys_arr_acc_add_ops_a[i].data_last      =  1'b0;
                    sys_arr_acc_add_ops_a[i].data_type      = TYPE_DATA;
                end else if(sys_arr_acc_bmm_first_del & bias_en & repl_bias) begin //bias is enabled, replicated, first bmm product, A = repl_bias
                    sys_arr_acc_add_ops_a[i].data_word      = sys_arr_acc_bias_repl.data_vect_words[i];
                    sys_arr_acc_add_ops_a[i].data_val       = sys_arr_acc_bias_repl.data_vect_val;
                    sys_arr_acc_add_ops_a[i].data_last      = sys_arr_acc_bias_repl.data_vect_last;
                    sys_arr_acc_add_ops_a[i].data_type      = sys_arr_acc_bias_repl.data_vect_type;
                end else begin //read from the memory
                    sys_arr_acc_add_ops_a[i].data_word      = sys_arr_acc_mem_if.data_out[i*C_ADD_ARITH_CFG.word_wdt +: C_ADD_ARITH_CFG.word_wdt];
                    sys_arr_acc_add_ops_a[i].data_val       = sys_arr_data_acc_del.data_vect_val;
                    sys_arr_acc_add_ops_a[i].data_last      = sys_arr_data_acc_del.data_vect_last;
                    sys_arr_acc_add_ops_a[i].data_type      = sys_arr_data_acc_del.data_vect_type;
                end
            end else if(sys_arr_data_acc_del.data_vect_type == TYPE_ACC_BIAS & sys_arr_data_acc_del.data_vect_val & !repl_bias & bias_en) begin
                sys_arr_acc_add_ops_b[i].data_word      = sys_arr_data_acc_del.data_vect_words[i];
                sys_arr_acc_add_ops_b[i].data_val       = sys_arr_data_acc_del.data_vect_val;
                sys_arr_acc_add_ops_b[i].data_last      = sys_arr_data_acc_del.data_vect_last;
                sys_arr_acc_add_ops_b[i].data_type      = sys_arr_data_acc_del.data_vect_type;
                sys_arr_acc_add_ops_a[i] = C_PIPE_DATA_RST_VAL;
            end else begin
                sys_arr_acc_add_ops_b[i] = C_PIPE_DATA_RST_VAL;
                sys_arr_acc_add_ops_a[i] = C_PIPE_DATA_RST_VAL;
            end

            if(sys_arr_acc_add_res[0].data_val & sys_arr_acc_add_res[0].data_type == TYPE_DATA) begin //results
                if(sys_arr_acc_bmm_last_del) begin //route to the output port
                    sys_arr_data_acc_out.data_vect_words[i] = sys_arr_acc_add_res[i].data_word;
                    sys_arr_data_acc_out.data_vect_last     = sys_arr_acc_add_res[i].data_last;
                    sys_arr_data_acc_out.data_vect_val      = sys_arr_acc_add_res[i].data_val;
                    sys_arr_data_acc_out.data_vect_type     = sys_arr_acc_add_res[i].data_type;
                    sys_arr_acc_mem_if.data_in = '0; //reset all the values in the acc. memory
                end else begin //write accumulation results to memory
                    sys_arr_data_acc_out = C_PIPE_DATA_VECT_RST_VAL;
                    sys_arr_acc_mem_if.data_in[i*C_ADD_ARITH_CFG.word_wdt +: C_ADD_ARITH_CFG.word_wdt] = sys_arr_acc_add_res[i].data_word;
                end
            end else if(sys_arr_acc_add_res[0].data_val & sys_arr_acc_add_res[0].data_type == TYPE_ACC_BIAS & !repl_bias & bias_en) begin //load bias
                sys_arr_data_acc_out = C_PIPE_DATA_VECT_RST_VAL;
                sys_arr_acc_mem_if.data_in[i*C_ADD_ARITH_CFG.word_wdt +: C_ADD_ARITH_CFG.word_wdt] = sys_arr_acc_add_res[i].data_word;
            end else begin //no valid data to write or to route to output port
                sys_arr_data_acc_out = C_PIPE_DATA_VECT_RST_VAL;
                sys_arr_acc_mem_if.data_in = '0;
            end
      end
end

genvar i;
generate
    for(i = 0; i < C_SYS_ARR_SIZE; i++) begin
        add_wrapp
        #(
            .ADD_ARITH_CFG(C_ADD_ARITH_CFG),
            .ADD_IN_CYC_LEN(C_ADD_FXP_IN_CYC_LEN),
            .ADD_OUT_CYC_LEN(C_ADD_FXP_OUT_CYC_LEN)
        )
        sys_arr_acc_vect_add
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .add_op_a(sys_arr_acc_add_ops_a[i]),   
            .add_op_b(sys_arr_acc_add_ops_b[i]),   
            .add_res(sys_arr_acc_add_res[i])
        );
    end
endgenerate

// synthesis translate_off

//assertions

//if the bias is replicated, then only a single vector is expected
assert property (@(posedge clk) disable iff (!rst_n) (bias_en & repl_bias & clk_en & sys_arr_data_to_acc.data_vect_val & sys_arr_data_to_acc.data_vect_type == TYPE_ACC_BIAS 
    |-> sys_arr_data_to_acc.data_vect_last)) else $error("If replicated bias is used, only a single vector is expected!");

//verify that with replicated bias and first bmm product, the register is populated with valid data
assert property (@(posedge clk) disable iff (!rst_n) (bias_en & repl_bias & clk_en & sys_arr_data_acc_del.data_vect_val & sys_arr_data_acc_del.data_vect_type == TYPE_DATA & sys_arr_acc_bmm_first_del 
    |-> ##1 sys_arr_acc_bias_repl.data_vect_val & sys_arr_acc_bias_repl.data_vect_type == TYPE_ACC_BIAS)) else $error("Expecting replicated bias register to contain valid data!");

//only biases or data are allowed inside accumulator
always @(posedge clk) assert (!(sys_arr_data_to_acc.data_vect_val & sys_arr_data_to_acc.data_vect_type != TYPE_ACC_BIAS & sys_arr_data_to_acc.data_vect_type != TYPE_DATA) | !rst_n)  else $error("Only moving values and bias shall be routed to the accumulator!");

//all side-channel info in shall be the same within a vector
always @(posedge clk) assert (side_ch_match_vect(sys_arr_acc_add_res) | !rst_n)  else $error("Side-channel info shall be the same within the accumulator vector adder output!");

// synthesis translate_on

endmodule