`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     tb_blck_proc_pipe
// Project Name:    Efficient FPGA CNN implementation
// Description:     Block level testbench for the processing pipeline
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;
import axi_if_pckg::*;

module tb_blck_proc_pipe;

logic        clk = 0;
logic        rst_n = 0;
logic        clk_en = 1;

bit halt_tb = 0;

pipe_data_vect_t upstream_data;
pipe_data_vect_t downstream_data;
proc_pipe_ctrl_if upstream_pipe_ctrl_if(); 
block_ctrl_if addr_gen_s_ctrl_if(); 
tens_trans_spec_t tens_trans_spec;
int bmm_limit;


logic [C_S_TDATA_WDT-1:0] S_AXIS_TDATA;
logic [C_S_TKEEP_WDT-1:0] S_AXIS_TKEEP;
logic S_AXIS_TLAST;
logic S_AXIS_TVALID;	
logic S_AXIS_TREADY;
logic [C_M_TDATA_WDT-1:0]  M_AXIS_TDATA;
logic [C_M_TKEEP_WDT-1:0]  M_AXIS_TKEEP;
logic M_AXIS_TLAST;
logic M_AXIS_TVALID;	
logic M_AXIS_TREADY;


// Clock generation
always 
#1.1ns 
if(~halt_tb)
clk = ~clk;

initial begin
  $timeformat(-9, 4, " ns", 14);
end

// Reset generation
initial begin
  clk_en = 1;
  //rst_n = 0;
  //#100ns rst_n = 1;
end

initial begin
    forever begin
        @(posedge clk);
        #1ps;
        M_AXIS_TREADY = $urandom_range(0,6) < 4;
    end
end

initial begin
    S_AXIS_TVALID = 0;
    #130ns;
    forever begin
        @(posedge clk);
        #2ps;
        S_AXIS_TVALID = $urandom_range(0,6) < 4;
    end
end

initial begin
    rst_n = 0;
    halt_tb = 0;
    S_AXIS_TDATA = 0;
    S_AXIS_TKEEP = '1;
    S_AXIS_TLAST = 0;

    #100ns;
    rst_n = 1;
    
    //->DEVICE
    //setup 
   //tens_trans_spec.tens_trans_cfg.tens_trans_type = TRANS_STREAM;
   //tens_trans_spec.tens_trans_cfg.nlin_f_type     = NLIN_F_RELU;
   //tens_trans_spec.tens_trans_cfg.batch_norm_en   = 1'b0;
   //tens_trans_spec.tens_trans_cfg.bias_en         = 1'b0;
   //tens_trans_spec.tens_trans_cfg.repl_bias       = 1'b0;
   //tens_trans_spec.tens_trans_lin_dims.tens_src_b_dims.tens_0_dim = 0; //[12x16] * [16x7]
   //tens_trans_spec.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim = 0;
   //tens_trans_spec.tens_trans_addrs.tens_src_a_addr      = 0;
   //tens_trans_spec.tens_trans_lin_dims.tens_res_dims.tens_0_dim = 3; //[12x16] * [16x7]
   //tens_trans_spec.tens_trans_lin_dims.tens_res_dims.tens_1_dim = 2;
   //tens_trans_spec.tens_trans_addrs.tens_res_addr        = 0;
   //addr_gen_s_ctrl_if.start = 1'b0;

   //#10ns;
   ////send start signal
   //#5ns;
   //@(posedge clk);
   //#1ps;
   //addr_gen_s_ctrl_if.start = 1'b1;
   //@(posedge clk);
   //#1ps;
   //addr_gen_s_ctrl_if.start = 1'b0;

   //#12ns;

   //forever begin
   //    @(posedge clk);
   //    #1ps;
   //    if(S_AXIS_TVALID & S_AXIS_TREADY)
   //        S_AXIS_TDATA++;
   //    S_AXIS_TLAST = S_AXIS_TDATA >= (tens_trans_spec.tens_trans_lin_dims.tens_res_dims.tens_0_dim*tens_trans_spec.tens_trans_lin_dims.tens_res_dims.tens_1_dim/(C_S_TDATA_WDT/C_BYTE_WDT))*(C_EXT_DATA_WORD_WDT/C_BYTE_WDT)*C_VECT_SIZE-1;
   //    if(S_AXIS_TDATA >= (tens_trans_spec.tens_trans_lin_dims.tens_res_dims.tens_0_dim*tens_trans_spec.tens_trans_lin_dims.tens_res_dims.tens_1_dim/(C_S_TDATA_WDT/C_BYTE_WDT))*(C_EXT_DATA_WORD_WDT/C_BYTE_WDT)*C_VECT_SIZE)
   //        break;
   //end

   //S_AXIS_TLAST = 0;
   //S_AXIS_TDATA = 0;

   //@(posedge clk);
   //#1ps;

   //#1us;

   //rst_n = 0;
   //#100ns;
   //rst_n = 1;

   ////setup 
   //tens_trans_spec.tens_trans_cfg.tens_trans_type = TRANS_LIN;
   //tens_trans_spec.tens_trans_cfg.nlin_f_type     = NLIN_F_RELU;
   //tens_trans_spec.tens_trans_cfg.batch_norm_en   = 1'b1;
   //tens_trans_spec.tens_trans_cfg.bias_en         = 1'b1;
   //tens_trans_spec.tens_trans_cfg.repl_bias       = 1'b1;
   //tens_trans_spec.tens_trans_lin_dims.tens_src_a_dims.tens_0_dim = 2; //[12x16] * [16x7]
   //tens_trans_spec.tens_trans_lin_dims.tens_src_a_dims.tens_1_dim = 9;
   //tens_trans_spec.tens_trans_lin_dims.tens_src_b_dims.tens_0_dim = 9;
   //tens_trans_spec.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim = 256;
   //tens_trans_spec.tens_trans_addrs.tens_batch_norm_addr = 255;
   //tens_trans_spec.tens_trans_addrs.tens_bias_addr       = 3;
   //tens_trans_spec.tens_trans_addrs.tens_src_a_addr      = 6;
   //tens_trans_spec.tens_trans_addrs.tens_src_b_addr      = 54;
   //tens_trans_spec.tens_trans_addrs.tens_res_addr        = 82;
   //addr_gen_s_ctrl_if.start = 1'b0;

   //#10ns;
   ////send start signal
   //#5ns;
   //@(posedge clk);
   //#1ps;
   //addr_gen_s_ctrl_if.start = 1'b1;
   //@(posedge clk);
   //#1ps;
   //addr_gen_s_ctrl_if.start = 1'b0;

   //#20us;

   //rst_n = 0;
   //#100ns;
   //rst_n = 1;

   //tens_trans_spec.tens_trans_cfg.tens_trans_type = TRANS_STREAM;
   //tens_trans_spec.tens_trans_cfg.nlin_f_type     = NLIN_F_RELU;
   //tens_trans_spec.tens_trans_cfg.batch_norm_en   = 1'b0;
   //tens_trans_spec.tens_trans_cfg.bias_en         = 1'b0;
   //tens_trans_spec.tens_trans_cfg.repl_bias       = 1'b0;
   //tens_trans_spec.tens_trans_lin_dims.tens_src_b_dims.tens_0_dim = 4; //[12x16] * [16x7]
   //tens_trans_spec.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim = 3;
   //tens_trans_spec.tens_trans_addrs.tens_src_b_addr      = 654;
   //tens_trans_spec.tens_trans_lin_dims.tens_res_dims.tens_0_dim = 3; //[12x16] * [16x7]
   //tens_trans_spec.tens_trans_lin_dims.tens_res_dims.tens_1_dim = 5;
   //tens_trans_spec.tens_trans_addrs.tens_res_addr        = 0;
   //addr_gen_s_ctrl_if.start = 1'b0;

   //#10ns;
   ////send start signal
   //#5ns;
   //@(posedge clk);
   //#1ps;
   //addr_gen_s_ctrl_if.start = 1'b1;
   //@(posedge clk);
   //#1ps;
   //addr_gen_s_ctrl_if.start = 1'b0;

   //#20ns;
   //forever begin
   //    @(posedge clk);
   //    #1ps;
   //    S_AXIS_TVALID = 1;
   //    S_AXIS_TLAST = S_AXIS_TDATA >= 3*5-1;
   //    if(S_AXIS_TVALID & S_AXIS_TREADY)
   //        S_AXIS_TDATA++;
   //    if(S_AXIS_TDATA >= 3*5)
   //        break;
   //end

   //S_AXIS_TLAST = 0;
   //S_AXIS_TDATA = 0;

   //@(posedge clk);
   //#1ps;

   //#1us;


    //#2us;
    //mmem_if_rd_port_mux = EXTERN;
    //repeat(100) begin
    //    @(posedge clk);
    //    #1ps;
    //    mmem_if_ext_rd_cmd.cmd_rd_en   = 1'b1;
    //    mmem_if_ext_rd_cmd.cmd_rd_addr = mmem_if_ext_rd_cmd.cmd_rd_addr + 1;
    //end

    ////batch param
    //for(int i = 0; i < 2; i++) begin
    //    @(posedge clk);
    //    #1ps;
    //    foreach(upstream_data.data_vect_words[j])
    //        upstream_data.data_vect_words[j] = 2+i;
    //    upstream_data.data_vect_val = 1'b1;
    //    upstream_data.data_vect_type = TYPE_BATCH_NORM_PARAM;
    //    upstream_data.data_vect_last = i == 1;
    //end
//
    ////biases, replicated
    //for(int i = 0; i < tens_trans_spec.tens_trans_dims.tens_res_dims.tens_0_dim*tens_trans_spec.tens_trans_dims.tens_res_dims.tens_1_dim; i++) begin
    //    @(posedge clk);
    //    #1ps;
    //    foreach(upstream_data.data_vect_words[j])
    //        upstream_data.data_vect_words[j] = i;
    //    upstream_data.data_vect_val   = 1'b1;
    //    upstream_data.data_vect_type  = TYPE_ACC_BIAS;
    //    upstream_data.data_vect_last  = i == tens_trans_spec.tens_trans_dims.tens_res_dims.tens_0_dim*tens_trans_spec.tens_trans_dims.tens_res_dims.tens_1_dim - 1; 
    //end
//
    //repeat(bmm_limit) begin
    //    //weights
    //    for(int i = 0; i < C_VECT_SIZE; i++) begin
    //        @(posedge clk);
    //        #1ps;
    //        foreach(upstream_data.data_vect_words[j])
    //            upstream_data.data_vect_words[j] = ((i*C_VECT_SIZE + j) % 10);
    //        upstream_data.data_vect_val   = 1'b1;
    //        upstream_data.data_vect_type  = TYPE_STAT_WEIGHT;
    //        upstream_data.data_vect_last  = i == C_VECT_SIZE-1;
    //    end
//
    //    //data
    //    for(int i = 0; i < tens_trans_spec.tens_trans_dims.tens_res_dims.tens_0_dim*tens_trans_spec.tens_trans_dims.tens_res_dims.tens_1_dim; i++) begin
    //        @(posedge clk);
    //        #1ps;
    //        foreach(upstream_data.data_vect_words[j])
    //            upstream_data.data_vect_words[j] = ((i*C_VECT_SIZE + j) % 10);
    //        upstream_data.data_vect_val   = 1'b1;
    //        upstream_data.data_vect_type  = TYPE_DATA;
    //        upstream_data.data_vect_last  = i == tens_trans_spec.tens_trans_dims.tens_res_dims.tens_0_dim*tens_trans_spec.tens_trans_dims.tens_res_dims.tens_1_dim - 1;
    //    end
    //end
//
    //@(posedge clk);
    //#1ps;
    //upstream_data = C_PIPE_DATA_RST_VAL;
    //#5000ns;
//
    //halt_tb = 1;
end

dig_top dut
(
    .clk(clk),
    .rst_n(rst_n),
    .S_AXIS_TDATA(S_AXIS_TDATA),
    .S_AXIS_TKEEP(S_AXIS_TKEEP),
    .S_AXIS_TLAST(S_AXIS_TLAST),
    .S_AXIS_TVALID(S_AXIS_TVALID),
    .S_AXIS_TREADY(S_AXIS_TREADY),
    .M_AXIS_TDATA(M_AXIS_TDATA),
    .M_AXIS_TKEEP(M_AXIS_TKEEP),
    .M_AXIS_TLAST(M_AXIS_TLAST),
    .M_AXIS_TVALID(M_AXIS_TVALID),
    .M_AXIS_TREADY(M_AXIS_TREADY)
);

endmodule