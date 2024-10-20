`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     addr_gen
// Project Name:    Efficient FPGA CNN implementation
// Description:     Address generation unit - based on the tensor transformation specification
//                  i.e. transformation type, tensor dimensions and other specification
//                  read and write adresses are generated for the read and write channels.
//                  The read and write channels are started together and operate in parallel and 
//                  independently. The read and write channels have different clock enables.
// 
//                  The address generation unit is started by the main FSM and it sends a done
//                  signal after both the read and write channels are done. It also sends
//                  a start signal to the systolic array to sample the necessary meta-data
//                  and receives a done signal from the main memory after the last write is finished
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;
import mem_pckg::*;
import perf_cnt_pckg::*;

module addr_gen
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    //control
    block_ctrl_if.slave           addr_gen_s_ctrl_if,
    block_ctrl_if.master          addr_gen_m_ctrl_if,
    block_ctrl_if.master          addr_gen_wr_port_ctrl,
    block_ctrl_if.master          addr_gen_rd_port_ctrl,
    block_ctrl_if.master          s_axis_ctrl,
    proc_pipe_ctrl_if.proc_block  addr_gen_rd_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_block  addr_gen_wr_pipe_ctrl_if,
    input  tens_trans_spec_t      tens_trans_spec,
    output tens_trans_spec_t      proc_pipe_tens_trans_spec,
    output logic [C_PERF_CNT_CNT-1:0]  perf_cnt_step_addr_gen,
    //TODO: add start signal for M & S FIFO, don't forget to add delay to match the command delay at minimum
    //data & address 
    output  mem_cmd_rd_t addr_gen_rd_mmem,
    output  mem_cmd_wr_t addr_gen_wr_mmem
);

//clock enables, resets
logic addr_gen_rst_n;
logic addr_gen_rd_clk_en;

assign addr_gen_rst_n = !(!rst_n | addr_gen_rd_pipe_ctrl_if.clear | addr_gen_wr_pipe_ctrl_if.clear);
assign addr_gen_rd_clk_en = addr_gen_rd_pipe_ctrl_if.step;
assign addr_gen_rd_pipe_ctrl_if.stall = 1'b0; //no stall, read addr gen block is the source

logic addr_gen_wr_clk_en;

assign addr_gen_wr_clk_en = addr_gen_wr_pipe_ctrl_if.step;
assign addr_gen_wr_pipe_ctrl_if.stall = !addr_gen_wr_pipe_ctrl_if.step; //simply propagate

logic addr_gen_busy;
logic addr_gen_rd_busy;
logic addr_gen_wr_busy;
logic addr_gen_m_ctrl_if_start_i;
tens_trans_spec_t tens_trans_spec_i;
tens_trans_spec_t tens_trans_spec_ii;

//register for the outputs of the primary index generation process
always_ff @(posedge clk) begin : addr_gen_ctrl_reg //control register for the response/sampling of data from the main FSM and from the processing pipeline
    if(!addr_gen_rst_n) begin
        tens_trans_spec_i           <= '0;
        tens_trans_spec_ii          <= '0;
        proc_pipe_tens_trans_spec   <= '0;
        addr_gen_m_ctrl_if_start_i  <= 1'b0;
        addr_gen_m_ctrl_if.start    <= 1'b0;
        addr_gen_s_ctrl_if.done     <= 1'b0;
        addr_gen_busy               <= 1'b0;
    end else begin
        if(addr_gen_rd_clk_en) begin
           addr_gen_m_ctrl_if_start_i <= 1'b0;
           addr_gen_s_ctrl_if.done    <= 1'b0;
           if(addr_gen_s_ctrl_if.start & !addr_gen_busy) begin //start signal from main FSM, sample tensor spec
                tens_trans_spec_i <= tens_trans_spec;
                addr_gen_m_ctrl_if_start_i <= 1'b1;
                addr_gen_s_ctrl_if.done    <= 1'b0;
                addr_gen_busy              <= 1'b1;
           end else if(addr_gen_busy & !addr_gen_rd_busy & !addr_gen_wr_busy & !addr_gen_m_ctrl_if_start_i) begin //all reads and writes done, assert done for the main FSM, return to idle state
                tens_trans_spec_i <= '0;
                addr_gen_s_ctrl_if.done    <= 1'b1;
                addr_gen_busy              <= 1'b0;
           end 
        end
        tens_trans_spec_ii        <= tens_trans_spec_i;
        addr_gen_m_ctrl_if.start  <= addr_gen_m_ctrl_if_start_i;
        proc_pipe_tens_trans_spec <= tens_trans_spec_i;
    end
end

//-------------------------------------------------------------
//Read chanel--------------------------------------------------
//-------------------------------------------------------------

pipe_data_type_t  addr_gen_rd_data_type;
logic addr_gen_rd_val;
logic addr_gen_rd_col_done;
logic addr_gen_rd_row_done;
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_col_i;  //column index
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_row_i;  //row index  
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_n_col_i;  //column index - batch norm param
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_n_row_i;  //row index - batch norm param
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_n_col_i_q;
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_n_row_i_q;
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_w_row_ul; //upper limit for the row index for stationary weight
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_b_col_i;  //column index - bias
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_b_row_i;  //row index - bias
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_b_col_i_q; 
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_b_row_i_q;
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_w_col_i;  //column index - stationary weight
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_w_row_i;  //row index - stationary weight
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_w_col_i_q; 
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_w_row_i_q; 
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_w_row_lim; //lower limit for the row index for stationary weight
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_w_row_lim_q;
logic                        addr_gen_rd_w_all_done; //all reads of stationary weight matrix are done
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_d_col_i;  //column index - data
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_d_row_i;  //row index - data
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_d_col_i_q;  
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_d_row_i_q;  
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_d_col_lim;
logic                        addr_gen_rd_d_col_lim_full; //column limit is set at max value (number of columns of data matrix)
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_d_col_rst;
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_d_col_rst_q;
logic addr_gen_rd_val_i;
logic addr_gen_rd_val_ii;
pipe_data_type_t  addr_gen_rd_data_type_i;
pipe_data_type_t  addr_gen_rd_data_type_ii;
logic addr_gen_rd_last;
logic addr_gen_rd_last_i;
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_col_ii;  
logic [C_TENS_INDEX_WDT-1:0] addr_gen_rd_row_ii;
mem_port_mux_t mmem_if_rd_port_mux;
mem_port_mux_t mmem_if_rd_port_mux_i;
mem_port_mux_t mmem_if_rd_port_mux_ii;

//Vector index generation of operands involved in
//operation: R = activ_function(batch_norm(A*B + b)) in case of linear/conv layer is done here.
//The entries of the operands are stored in vectors and are stored either column-first or row-first
//Specifically, the operands involved are:
//batch norm params (column-first)
//A matrix - the stationary weights (row-first)
//B matrix - the moving values (column-first)
//b matrix - the bias (column-first)
//
//The matrix multiplication and addition is done in a block-wise manner,
//a typical flow of a computing a single block of the result is:
//Start by main FSM -> generate batch param indices -> generate bias indices -> 
//generate weight indices -> generate data indices -> generate weight indices ->
//generate data indices -> ... -> generate data indices
//
//An effort is made here to only increment the indices by constants to not create any
//critical path bottlenecks. The conversion between 2D indices and a linear index (address)
//which requires multiplication is done afterwards in a pipelined manner

always_ff @(posedge clk) begin : addr_gen_rd_prim_index
    if(!addr_gen_rst_n) begin
        addr_gen_rd_busy            <= 1'b0;
        addr_gen_rd_data_type       <= '0;
        addr_gen_rd_val             <= 1'b0;
        addr_gen_rd_w_col_i         <= '0;
        addr_gen_rd_w_row_i         <= C_VECT_SIZE-1;
        addr_gen_rd_w_row_lim       <= '0;
        addr_gen_rd_w_all_done      <= 1'b0;
        addr_gen_rd_d_col_lim       <= '0;
        addr_gen_rd_d_col_lim_full  <= 1'b0;
        addr_gen_rd_d_col_rst       <= '0;
        addr_gen_rd_b_col_i         <= '0;
        addr_gen_rd_b_row_i         <= '0;
        addr_gen_rd_d_col_i         <= '0;
        addr_gen_rd_d_row_i         <= '0;
        addr_gen_rd_n_col_i         <= '0;        
        addr_gen_rd_n_row_i         <= '0;
        addr_gen_rd_last            <= 1'b0;
        mmem_if_rd_port_mux         <= IDLE;
    end else begin
        if(addr_gen_rd_clk_en) begin
            if(addr_gen_m_ctrl_if_start_i & !addr_gen_rd_busy) begin //start command from main FSM - initial state
                if(tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_STREAM) begin //streaming read - C2H based on dimensions of src_a/src_b, if all are zero then no C2H to be done
                    if(tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_0_dim == tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_1_dim & tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_0_dim == '0) begin
                        addr_gen_rd_busy           <= 1'b0;
                        addr_gen_rd_val            <= 1'b0;
                        mmem_if_rd_port_mux        <= IDLE;
                    end else begin
                        addr_gen_rd_busy           <= 1'b1;
                        addr_gen_rd_val            <= 1'b1;
                        mmem_if_rd_port_mux        <= EXTERN;
                        addr_gen_rd_data_type      <= TYPE_DATA;
                    end
                end else if(tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_LIN | tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_CONV) begin
                    addr_gen_rd_d_col_lim      <= tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim > C_SYS_ARR_ACC_MEM_SIZE ? C_SYS_ARR_ACC_MEM_SIZE : tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim; //setup data column limit = min(col_cnt(B), MAX_ACC_SIZE)
                    addr_gen_rd_d_col_lim_full <= tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim <= C_SYS_ARR_ACC_MEM_SIZE;
                    addr_gen_rd_busy           <= 1'b1;
                    addr_gen_rd_val            <= 1'b1;
                    mmem_if_rd_port_mux        <= INTERN;
                    case ({tens_trans_spec_i.tens_trans_cfg.batch_norm_en, tens_trans_spec_i.tens_trans_cfg.bias_en}) //figure out what is the initial state
                        2'b00: begin 
                            addr_gen_rd_data_type <= TYPE_STAT_WEIGHT;
                        end
                        2'b01: begin 
                            addr_gen_rd_data_type <= TYPE_ACC_BIAS;
                        end
                        2'b10: begin 
                            addr_gen_rd_data_type <= TYPE_BATCH_NORM_PARAM;
                        end
                        2'b11: begin 
                            addr_gen_rd_data_type <= TYPE_BATCH_NORM_PARAM;
                        end
                    endcase
                end else begin //maxpooling transformation
                    addr_gen_rd_busy           <= 1'b1;
                    addr_gen_rd_val            <= 1'b1;
                    mmem_if_rd_port_mux        <= INTERN;
                    addr_gen_rd_data_type      <= TYPE_DATA;
                end
            end else if(addr_gen_rd_busy) begin
                if(tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_STREAM) begin //index generation for C2H stream
                    if(!addr_gen_rd_last) begin
                        addr_gen_rd_row_done   = addr_gen_rd_d_row_i >= tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_0_dim-1;
                        addr_gen_rd_col_done   = addr_gen_rd_d_col_i >= tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_1_dim-1;
                        addr_gen_rd_d_col_i_q  = addr_gen_rd_col_done ? '0 : addr_gen_rd_d_col_i + 1;
                        addr_gen_rd_d_row_i_q  = (addr_gen_rd_col_done & addr_gen_rd_row_done) ? '0 : (addr_gen_rd_col_done ? addr_gen_rd_d_row_i + 1 : addr_gen_rd_d_row_i);
                        addr_gen_rd_d_col_i   <= addr_gen_rd_d_col_i_q;    
                        addr_gen_rd_d_row_i   <= addr_gen_rd_d_row_i_q;
                        addr_gen_rd_val       <= !(addr_gen_rd_row_done & addr_gen_rd_col_done);
                        addr_gen_rd_last      <= addr_gen_rd_row_done & addr_gen_rd_col_done;    //done, generate last flag
                    end else if(addr_gen_rd_busy & !addr_gen_rd_port_ctrl.done) begin //wait for the done flag from the memory interface
                        addr_gen_rd_busy      <= 1'b1; 
                        addr_gen_rd_val       <= 1'b0;
                    end else begin
                        addr_gen_rd_busy      <= 1'b0;  //done, deassert busy flag and reset state
                    end
                end else if(tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_LIN | tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_CONV) begin //index generation for linear of conv transformation
                    case (addr_gen_rd_data_type) 
                        TYPE_BATCH_NORM_PARAM: begin //two batch norm param read per bmm dot product
                            addr_gen_rd_row_done    = addr_gen_rd_n_row_i >= tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_0_dim-1;
                            addr_gen_rd_col_done    = addr_gen_rd_n_col_i == 1;  //first column is scale, second is offset
                            addr_gen_rd_n_col_i_q   = addr_gen_rd_col_done ? '0 : addr_gen_rd_n_col_i + 1;
                            addr_gen_rd_n_row_i_q   = addr_gen_rd_col_done ? addr_gen_rd_n_row_i + 1 : addr_gen_rd_n_row_i;           
                            addr_gen_rd_n_col_i     <= addr_gen_rd_n_col_i_q;
                            addr_gen_rd_n_row_i     <= addr_gen_rd_n_row_i_q;
                            addr_gen_rd_val         <= 1'b1;
                            if(!addr_gen_rd_col_done) begin //one more read to do
                                addr_gen_rd_data_type   <= TYPE_BATCH_NORM_PARAM;
                                addr_gen_rd_last        <= 1'b0;
                            end else if(tens_trans_spec_i.tens_trans_cfg.bias_en) begin
                                addr_gen_rd_data_type   <= TYPE_ACC_BIAS;
                                addr_gen_rd_last        <= 1'b1;
                            end else begin
                                addr_gen_rd_data_type   <= TYPE_STAT_WEIGHT;
                                addr_gen_rd_last        <= 1'b1;
                            end
                        end
                        TYPE_ACC_BIAS: begin //either read a single column block tensor or just a single bias column which will be replicated
                            addr_gen_rd_row_done = addr_gen_rd_b_row_i >= tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_0_dim-1;
                            if(tens_trans_spec_i.tens_trans_cfg.repl_bias)
                                addr_gen_rd_col_done = addr_gen_rd_d_col_lim_full;
                            else 
                                addr_gen_rd_col_done = addr_gen_rd_b_col_i >= addr_gen_rd_d_col_lim-1 & addr_gen_rd_d_col_lim_full;
                            addr_gen_rd_b_col_i_q     = addr_gen_rd_col_done | tens_trans_spec_i.tens_trans_cfg.repl_bias ? '0 : addr_gen_rd_b_col_i + 1;
                            addr_gen_rd_b_row_i_q     = addr_gen_rd_col_done ? addr_gen_rd_b_row_i + 1 : addr_gen_rd_b_row_i;           
                            addr_gen_rd_b_col_i       <= addr_gen_rd_b_col_i_q;
                            addr_gen_rd_b_row_i       <= addr_gen_rd_b_row_i_q;
                            addr_gen_rd_val           <= 1'b1;
                            if(!tens_trans_spec_i.tens_trans_cfg.repl_bias & addr_gen_rd_b_col_i >= addr_gen_rd_d_col_lim-1 | tens_trans_spec_i.tens_trans_cfg.repl_bias) begin
                                addr_gen_rd_data_type   <= TYPE_STAT_WEIGHT;
                                addr_gen_rd_last        <= 1'b1;
                            end else begin
                                addr_gen_rd_data_type   <= TYPE_ACC_BIAS;
                                addr_gen_rd_last        <= 1'b0;
                            end
                        end
                        TYPE_STAT_WEIGHT: begin //always read a C_VECT*C_VECT block of A data
                            addr_gen_rd_row_done    = addr_gen_rd_w_row_i == addr_gen_rd_w_row_lim;
                            addr_gen_rd_col_done    = addr_gen_rd_w_col_i >= tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_1_dim-1;
                            if(addr_gen_rd_row_done & addr_gen_rd_col_done) begin
                                addr_gen_rd_w_col_i_q   = '0;
                                if(addr_gen_rd_w_row_lim == C_VECT_SIZE*(tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_0_dim - 1) & addr_gen_rd_d_col_lim_full) begin
                                    addr_gen_rd_w_row_lim_q  = '0; //all done, reset
                                    addr_gen_rd_w_all_done  <= 1'b1;
                                end else if(addr_gen_rd_d_col_lim_full) begin
                                    addr_gen_rd_w_row_lim_q = addr_gen_rd_w_row_lim + C_VECT_SIZE; //B column blocks done
                                end else begin
                                    addr_gen_rd_w_row_lim_q = addr_gen_rd_w_row_lim; //B column blocks remaining
                                end
                            end else if(addr_gen_rd_row_done) begin
                                addr_gen_rd_w_col_i_q   = addr_gen_rd_w_col_i + 1;
                                addr_gen_rd_w_row_lim_q = addr_gen_rd_w_row_lim;
                            end else begin
                                addr_gen_rd_w_col_i_q   = addr_gen_rd_w_col_i;
                                addr_gen_rd_w_row_lim_q = addr_gen_rd_w_row_lim;
                            end
                            addr_gen_rd_w_row_lim   <= addr_gen_rd_w_row_lim_q;
                            addr_gen_rd_w_row_i_q    = addr_gen_rd_row_done ? (addr_gen_rd_w_row_lim_q + C_VECT_SIZE-1) : addr_gen_rd_w_row_i - 1;           
                            addr_gen_rd_w_col_i     <= addr_gen_rd_w_col_i_q;
                            addr_gen_rd_w_row_i     <= addr_gen_rd_w_row_i_q;
                            addr_gen_rd_val         <= 1'b1;
                            if(addr_gen_rd_row_done) begin
                                addr_gen_rd_data_type   <= TYPE_DATA;
                                addr_gen_rd_last        <= 1'b1;
                            end else begin
                                addr_gen_rd_data_type   <= TYPE_STAT_WEIGHT;
                                addr_gen_rd_last        <= 1'b0;
                            end 
                        end
                        TYPE_DATA: begin //read a single column block of B matrix
                            addr_gen_rd_row_done    = addr_gen_rd_d_row_i >= tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_0_dim-1;
                            addr_gen_rd_col_done    = addr_gen_rd_d_col_i >= addr_gen_rd_d_col_lim-1;
                            addr_gen_rd_val         <= 1'b1;
                            if(addr_gen_rd_row_done & addr_gen_rd_col_done & addr_gen_rd_w_all_done & addr_gen_rd_d_col_lim_full) begin //all done, reset
                                addr_gen_rd_busy            <= 1'b0; //done, disable busy flag, leading to a reset
                                addr_gen_rd_last            <= 1'b1; //done, generate final last flag
                                mmem_if_rd_port_mux         <= IDLE;
                            end else if(addr_gen_rd_row_done & addr_gen_rd_col_done & addr_gen_rd_d_col_lim_full) begin //end of bm product, B column blocks done
                                addr_gen_rd_d_row_i_q    = '0;
                                addr_gen_rd_d_row_i     <= addr_gen_rd_d_row_i_q;
                                //update the column limit and reset values
                                addr_gen_rd_d_col_lim      <= tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim > C_SYS_ARR_ACC_MEM_SIZE ? C_SYS_ARR_ACC_MEM_SIZE : tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim; //setup data column limit = min(col_cnt(B), MAX_ACC_SIZE)
                                addr_gen_rd_d_col_lim_full <= tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim <= C_SYS_ARR_ACC_MEM_SIZE;
                                addr_gen_rd_d_col_rst_q     = '0;
                                addr_gen_rd_d_col_rst      <= addr_gen_rd_d_col_rst_q;
                                addr_gen_rd_d_col_i_q       = addr_gen_rd_d_col_rst_q;
                                addr_gen_rd_d_col_i        <= addr_gen_rd_d_col_i_q;
                                addr_gen_rd_last           <= 1'b1;
                                case ({tens_trans_spec_i.tens_trans_cfg.batch_norm_en, tens_trans_spec_i.tens_trans_cfg.bias_en}) //figure out what is the initial state
                                    2'b00: begin 
                                        addr_gen_rd_data_type <= TYPE_STAT_WEIGHT;
                                    end
                                    2'b01: begin 
                                        addr_gen_rd_data_type <= TYPE_ACC_BIAS;
                                    end
                                    2'b10: begin 
                                        addr_gen_rd_data_type <= TYPE_BATCH_NORM_PARAM;
                                    end
                                    2'b11: begin 
                                        addr_gen_rd_data_type <= TYPE_BATCH_NORM_PARAM;
                                    end
                                endcase
                            end else if(addr_gen_rd_row_done & addr_gen_rd_col_done) begin //end of bm product, B column blocks remaining
                                addr_gen_rd_d_row_i_q    = '0;
                                addr_gen_rd_d_row_i     <= addr_gen_rd_d_row_i_q;
                                //update the column limit and reset values
                                addr_gen_rd_d_col_lim      <= addr_gen_rd_d_col_lim + C_SYS_ARR_ACC_MEM_SIZE > tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim ? tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim : addr_gen_rd_d_col_lim + C_SYS_ARR_ACC_MEM_SIZE;
                                addr_gen_rd_d_col_lim_full <= (addr_gen_rd_d_col_lim + C_SYS_ARR_ACC_MEM_SIZE > tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim ? tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim : addr_gen_rd_d_col_lim + C_SYS_ARR_ACC_MEM_SIZE) == tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim;
                                addr_gen_rd_d_col_rst_q     = addr_gen_rd_d_col_rst + C_SYS_ARR_ACC_MEM_SIZE;
                                addr_gen_rd_d_col_rst      <= addr_gen_rd_d_col_rst_q;
                                addr_gen_rd_d_col_i_q       = addr_gen_rd_d_col_rst_q;
                                addr_gen_rd_d_col_i        <= addr_gen_rd_d_col_i_q;
                                addr_gen_rd_data_type      <= TYPE_ACC_BIAS;
                                addr_gen_rd_last           <= 1'b1;
                            end else if(addr_gen_rd_col_done) begin
                                addr_gen_rd_d_row_i_q    = addr_gen_rd_d_row_i + 1;
                                addr_gen_rd_d_row_i     <= addr_gen_rd_d_row_i_q;
                                addr_gen_rd_d_col_i_q    = addr_gen_rd_d_col_rst;
                                addr_gen_rd_d_col_i     <= addr_gen_rd_d_col_i_q;
                                addr_gen_rd_data_type   <= TYPE_STAT_WEIGHT;
                                addr_gen_rd_last        <= 1'b1;
                            end else begin
                                addr_gen_rd_d_col_i_q    = addr_gen_rd_d_col_i + 1;
                                addr_gen_rd_d_col_i     <= addr_gen_rd_d_col_i_q;
                                addr_gen_rd_data_type   <= TYPE_DATA;
                                addr_gen_rd_last        <= 1'b0;
                            end
                        end
                    endcase
                end else begin //maxpooling
                    if(!addr_gen_rd_last) begin
                        addr_gen_rd_row_done   = addr_gen_rd_d_row_i >= tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_0_dim-1;
                        addr_gen_rd_col_done   = addr_gen_rd_d_col_i >= tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim-1;
                        addr_gen_rd_d_row_i_q  = addr_gen_rd_row_done ? '0 : addr_gen_rd_d_row_i + 1;
                        addr_gen_rd_d_col_i_q  = (addr_gen_rd_col_done & addr_gen_rd_row_done) ? '0 : (addr_gen_rd_row_done ? addr_gen_rd_d_col_i + 1 : addr_gen_rd_d_col_i);
                        addr_gen_rd_d_col_i   <= addr_gen_rd_d_col_i_q;    
                        addr_gen_rd_d_row_i   <= addr_gen_rd_d_row_i_q;
                        addr_gen_rd_val       <= !(addr_gen_rd_row_done & addr_gen_rd_col_done);
                        addr_gen_rd_last      <= addr_gen_rd_row_done & addr_gen_rd_col_done;    //done, generate last flag
                    end else begin //read port channel done
                        addr_gen_rd_busy      <= 1'b0; 
                        addr_gen_rd_val       <= 1'b0;
                    end 
                end


            end else begin //if not busy, keep everything in reset
                addr_gen_rd_busy            <= 1'b0;
                addr_gen_rd_data_type       <= '0;
                addr_gen_rd_val             <= 1'b0;
                addr_gen_rd_w_col_i         <= '0;
                addr_gen_rd_w_row_i         <= C_VECT_SIZE-1;
                addr_gen_rd_w_row_lim       <= '0;
                addr_gen_rd_w_all_done      <= 1'b0;
                addr_gen_rd_d_col_lim       <= '0;
                addr_gen_rd_d_col_lim_full  <= 1'b0;
                addr_gen_rd_d_col_rst       <= '0;
                addr_gen_rd_b_col_i         <= '0;
                addr_gen_rd_b_row_i         <= '0;
                addr_gen_rd_d_col_i         <= '0;
                addr_gen_rd_d_row_i         <= '0;
                addr_gen_rd_n_col_i         <= '0;        
                addr_gen_rd_n_row_i         <= '0;
                addr_gen_rd_last            <= 1'b0;
                mmem_if_rd_port_mux         <= IDLE;
            end
        end
    end
end

//register for muxing between the different indices, register the side channel information
always_ff @(posedge clk) begin : addr_gen_rd_index_mux
    if(!addr_gen_rst_n) begin
        addr_gen_rd_col_i           <= '0;
        addr_gen_rd_row_i           <= '0;
        addr_gen_rd_col_ii          <= '0;
        addr_gen_rd_row_ii          <= '0;
        addr_gen_rd_data_type_i     <= '0;
        addr_gen_rd_val_i           <= 1'b0;
        mmem_if_rd_port_mux_i       <= IDLE;
        addr_gen_rd_data_type_ii    <= '0;
        addr_gen_rd_val_ii          <= 1'b0;
        mmem_if_rd_port_mux_ii      <= IDLE;
        addr_gen_rd_last_i          <= 1'b0;
    end else begin
        if(addr_gen_rd_clk_en) begin
            if(addr_gen_rd_val) begin
                case (addr_gen_rd_data_type) 
                        TYPE_BATCH_NORM_PARAM: begin 
                            addr_gen_rd_col_i <= addr_gen_rd_n_col_i;
                            addr_gen_rd_row_i <= addr_gen_rd_n_row_i;
                        end
                        TYPE_ACC_BIAS: begin 
                            addr_gen_rd_col_i <= addr_gen_rd_b_col_i;
                            addr_gen_rd_row_i <= addr_gen_rd_b_row_i;
                        end
                        TYPE_STAT_WEIGHT: begin 
                            addr_gen_rd_col_i <= addr_gen_rd_w_col_i;
                            addr_gen_rd_row_i <= addr_gen_rd_w_row_i;
                        end
                        TYPE_DATA: begin 
                            addr_gen_rd_col_i <= addr_gen_rd_d_col_i;
                            addr_gen_rd_row_i <= addr_gen_rd_d_row_i;
                        end
                    endcase
            end else begin
                addr_gen_rd_col_i           <= '0;
                addr_gen_rd_row_i           <= '0;
            end
            //delay to math latency of row_i and col_i
            addr_gen_rd_data_type_i     <= addr_gen_rd_data_type;    
            addr_gen_rd_val_i           <= addr_gen_rd_val;
            mmem_if_rd_port_mux_i       <= mmem_if_rd_port_mux;
            //one more register stage
            addr_gen_rd_col_ii          <= addr_gen_rd_col_i;        
            addr_gen_rd_row_ii          <= addr_gen_rd_row_i;
            addr_gen_rd_data_type_ii    <= addr_gen_rd_data_type_i;    
            addr_gen_rd_val_ii          <= addr_gen_rd_val_i;
            mmem_if_rd_port_mux_ii      <= mmem_if_rd_port_mux_i;
            addr_gen_rd_last_i          <= addr_gen_rd_last;
        end
    end
end

logic [C_TENS_INDEX_WDT-1:0] conv_addr_gen_row_i;
logic [C_TENS_INDEX_WDT-1:0] conv_addr_gen_col_i;
logic                        conv_addr_gen_val;
mem_cmd_rd_t                 conv_addr_gen_rd_mmem;
mem_cmd_rd_t                 conv_addr_gen_rd_mmem_q;

always_comb begin : comp_addr_conv_proc_in_mux
    if(addr_gen_rd_clk_en & addr_gen_rd_val_ii & ((tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_CONV & addr_gen_rd_data_type_ii == TYPE_DATA) | (tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_MAXPOOL & addr_gen_rd_data_type_ii == TYPE_DATA))) begin //valid conv indices
        conv_addr_gen_rd_mmem.cmd_rd_en                     = 1'b1;
        conv_addr_gen_rd_mmem.cmd_rd_data_vect_type         = addr_gen_rd_data_type_ii;
        conv_addr_gen_rd_mmem.cmd_rd_port_mux               = mmem_if_rd_port_mux_ii;
        conv_addr_gen_rd_mmem.cmd_rd_data_vect_zero_padd    = 1'b0;
        conv_addr_gen_rd_mmem.cmd_rd_data_vect_neg_inf_padd = 1'b0;
        conv_addr_gen_rd_mmem.cmd_rd_data_vect_last         = addr_gen_rd_last_i;
        conv_addr_gen_rd_mmem.cmd_rd_addr                   = '0;
        conv_addr_gen_row_i                                 = addr_gen_rd_row_ii;
        conv_addr_gen_col_i                                 = addr_gen_rd_col_ii;
        conv_addr_gen_val                                   = 1'b1;
    end else begin
        conv_addr_gen_rd_mmem  = '0;
        conv_addr_gen_row_i    = '0;
        conv_addr_gen_col_i    = '0;
        conv_addr_gen_val      = '0;
    end
end

conv_addr_gen conv_addr_gen_inst
(
    .clk(clk),
    .rst_n(addr_gen_rst_n),
    .clk_en(addr_gen_rd_clk_en),
    .conv_tens_trans_spec(tens_trans_spec_ii),
    .conv_addr_gen_rd_mmem(conv_addr_gen_rd_mmem),
    .conv_addr_gen_row_i(conv_addr_gen_row_i),
    .conv_addr_gen_col_i(conv_addr_gen_col_i),
    .conv_addr_gen_val(conv_addr_gen_val),
    .conv_addr_gen_rd_mmem_q(conv_addr_gen_rd_mmem_q)
);

logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_add_op_a; 
logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_add_op_b; 
logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_mult_op_a; 
logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_mult_op_b;      
mem_cmd_rd_t addr_gen_rd_mmem_i;
mem_cmd_rd_t addr_gen_rd_mmem_q;
mem_cmd_rd_t addr_gen_lin_rd_mmem_q;

always_comb begin : comp_addr_lin_proc_in_mux
    if(addr_gen_rd_clk_en & addr_gen_rd_val_ii & (tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_LIN | tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_STREAM | (tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_CONV & addr_gen_rd_data_type_ii != TYPE_DATA))) begin //valid linear indices 
        addr_gen_rd_mmem_i.cmd_rd_en                     = 1'b1;
        addr_gen_rd_mmem_i.cmd_rd_data_vect_type         = addr_gen_rd_data_type_ii;
        addr_gen_rd_mmem_i.cmd_rd_port_mux               = mmem_if_rd_port_mux_ii;
        addr_gen_rd_mmem_i.cmd_rd_data_vect_zero_padd    = 1'b0;
        addr_gen_rd_mmem_i.cmd_rd_data_vect_neg_inf_padd = 1'b0;
        addr_gen_rd_mmem_i.cmd_rd_data_vect_last         = addr_gen_rd_last_i;
        addr_gen_rd_mmem_i.cmd_rd_addr                   = '0;
        casez (addr_gen_rd_data_type_ii)
            TYPE_BATCH_NORM_PARAM : begin
                addr_gen_rd_mult_op_a    = addr_gen_rd_row_ii;
                addr_gen_rd_mult_op_b    = 2; //always two columns
                addr_gen_rd_add_op_a     = addr_gen_rd_col_ii;
                addr_gen_rd_add_op_b     = tens_trans_spec_i.tens_trans_addrs.tens_batch_norm_addr;
            end 
            TYPE_ACC_BIAS : begin
                addr_gen_rd_mult_op_a    = addr_gen_rd_row_ii;
                if(tens_trans_spec_i.tens_trans_cfg.bias_en & tens_trans_spec_i.tens_trans_cfg.repl_bias)
                    addr_gen_rd_mult_op_b    = 1; //bias is replicated, has only one column
                else
                    addr_gen_rd_mult_op_b    = tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim;
                addr_gen_rd_add_op_a     = addr_gen_rd_col_ii;
                addr_gen_rd_add_op_b     = tens_trans_spec_i.tens_trans_addrs.tens_bias_addr;
            end
            TYPE_STAT_WEIGHT : begin
                addr_gen_rd_mult_op_a    = addr_gen_rd_col_ii;
                addr_gen_rd_mult_op_b    = tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_0_dim*C_VECT_SIZE;
                addr_gen_rd_add_op_a     = addr_gen_rd_row_ii;
                addr_gen_rd_add_op_b     = tens_trans_spec_i.tens_trans_addrs.tens_src_a_addr;
            end
            TYPE_DATA : begin //in case of streaming (C2H) we are using src_a dimension/address, otherwise src_b 
                addr_gen_rd_mult_op_a    = addr_gen_rd_row_ii;
                addr_gen_rd_mult_op_b    = tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_STREAM ? tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_1_dim : tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim;
                addr_gen_rd_add_op_a     = addr_gen_rd_col_ii;
                addr_gen_rd_add_op_b     = tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_STREAM ? tens_trans_spec_i.tens_trans_addrs.tens_src_a_addr : tens_trans_spec_i.tens_trans_addrs.tens_src_b_addr;
            end
            default : begin
                addr_gen_rd_mult_op_a    = '0;
                addr_gen_rd_mult_op_b    = '0;
                addr_gen_rd_add_op_a     = '0;
                addr_gen_rd_add_op_b     = '0;
            end
        endcase
    end else begin
        addr_gen_rd_mmem_i       = '0;
        addr_gen_rd_mult_op_a    = '0;
        addr_gen_rd_mult_op_b    = '0;
        addr_gen_rd_add_op_a     = '0;
        addr_gen_rd_add_op_b     = '0;
    end
end

lin_addr_gen lin_addr_gen_rd_inst
(
    .clk(clk),
    .rst_n(addr_gen_rst_n),
    .clk_en(addr_gen_rd_clk_en),
    .lin_tens_trans_spec(tens_trans_spec_ii),
    .addr_gen_rd_mmem_i(addr_gen_rd_mmem_i),
    .addr_gen_rd_mult_op_a(addr_gen_rd_mult_op_a),
    .addr_gen_rd_mult_op_b(addr_gen_rd_mult_op_b),
    .addr_gen_rd_add_op_a(addr_gen_rd_add_op_a),
    .addr_gen_rd_add_op_b(addr_gen_rd_add_op_b),
    .addr_gen_lin_rd_mmem_q(addr_gen_lin_rd_mmem_q)
);

always_comb begin //mux between linear and convolutional address
    addr_gen_rd_mmem_q = '0;
    
    if(addr_gen_lin_rd_mmem_q.cmd_rd_en) begin
        addr_gen_rd_mmem_q = addr_gen_lin_rd_mmem_q;
    end else if(conv_addr_gen_rd_mmem_q.cmd_rd_en) begin
        addr_gen_rd_mmem_q = conv_addr_gen_rd_mmem_q;
    end
end

del_chain //final delay chain for the mmem read command
#(
    .IN_WORD_WDT($bits(addr_gen_rd_mmem_i)),
    .DEL_CYC_LEN(C_ADDR_GEN_RD_MMEM_CMD_CYC_LEN)
)
addr_gen_rd_mem_del_chain
(
    .clk(clk),
    .rst_n(addr_gen_rst_n),
    .clk_en(addr_gen_rd_clk_en),
    .in_word(addr_gen_rd_mmem_q),
    .in_word_val(),
    .in_word_del(addr_gen_rd_mmem),
    .in_word_val_del()
);

//-------------------------------------------------------------
//Write chanel-------------------------------------------------
//-------------------------------------------------------------

//writing channel is trivial, because the computed data emerges
//from the proc. pipeline in column first order, we simply iterate
//the write address until the end of the result matrix has been reached
//afterwards we extend the address and add the result offset

logic [C_TENS_INDEX_WDT-1:0] addr_gen_wr_lin_i;
logic [C_TENS_INDEX_WDT-1:0] addr_gen_wr_lin_lim;
mem_cmd_wr_t addr_gen_wr_mmem_q;

logic [C_MMEM_ADDR_WDT-1:0] addr_gen_wr_fin_add_op_a;
logic [C_MMEM_ADDR_WDT-1:0] addr_gen_wr_fin_add_op_b;

logic addr_gen_wr_val;
logic addr_gen_wr_last;
mem_port_mux_t mmem_if_wr_port_mux;


always_ff @(posedge clk) begin : addr_gen_wr_prim_index
    if(!addr_gen_rst_n) begin
        addr_gen_wr_busy        <= 1'b0;
        addr_gen_wr_lin_i       <= '0;
        addr_gen_wr_lin_lim     <= '0;
        addr_gen_wr_val         <= 1'b0;
        mmem_if_wr_port_mux     <= IDLE;
        s_axis_ctrl.start       <= 1'b0;
    end else begin
        if(addr_gen_wr_clk_en) begin
           if(addr_gen_m_ctrl_if_start_i & !addr_gen_wr_busy) begin //start generating write addresses (cycle later than read channel)
                if(tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_STREAM) begin //streaming read - H2C based on dimensions of res, if all are zero then no H2C to be done
                    if(tens_trans_spec_i.tens_trans_lin_dims.tens_res_dims.tens_0_dim == tens_trans_spec_i.tens_trans_lin_dims.tens_res_dims.tens_1_dim & tens_trans_spec_i.tens_trans_lin_dims.tens_res_dims.tens_0_dim == '0) begin
                        addr_gen_wr_busy           <= 1'b0;
                        addr_gen_wr_val            <= 1'b0;
                        mmem_if_wr_port_mux        <= IDLE;
                    end else begin
                        addr_gen_wr_busy           <= 1'b1;
                        addr_gen_wr_val            <= 1'b1;
                        addr_gen_wr_lin_i          <= '0;
                        addr_gen_wr_lin_lim        <= tens_trans_spec_i.tens_trans_lin_dims.tens_res_dims.tens_0_dim * tens_trans_spec_i.tens_trans_lin_dims.tens_res_dims.tens_1_dim; //compute the lin. index limit
                        mmem_if_wr_port_mux        <= EXTERN;
                        s_axis_ctrl.start          <= 1'b1; //start the S_AXIS port
                    end
                end else if(tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_LIN | tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_CONV | tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_MAXPOOL) begin
                    addr_gen_wr_busy    <= 1'b1;
                    addr_gen_wr_val     <= 1'b1;
                    addr_gen_wr_lin_lim <= tens_trans_spec_i.tens_trans_lin_dims.tens_res_dims.tens_0_dim * tens_trans_spec_i.tens_trans_lin_dims.tens_res_dims.tens_1_dim; //compute the lin. index limit
                    mmem_if_wr_port_mux <= INTERN;
                end
           end else if(addr_gen_wr_busy & addr_gen_wr_lin_i + 1 < addr_gen_wr_lin_lim) begin //iterate index
                addr_gen_wr_lin_i <= addr_gen_wr_lin_i + 1;
                addr_gen_wr_val   <= 1'b1;
                s_axis_ctrl.start <= 1'b0; //deassert start flag
           end else if (addr_gen_wr_busy & !addr_gen_wr_port_ctrl.done) begin //index at limit, but not done signal from the wr port
                addr_gen_wr_val   <= 1'b0;
                s_axis_ctrl.start <= 1'b0; //deassert start flag
           end else if(addr_gen_wr_busy & addr_gen_wr_port_ctrl.done) begin //done signal received, reset all
                addr_gen_wr_busy        <= 1'b0;
                addr_gen_wr_lin_i       <= '0;
                addr_gen_wr_lin_lim     <= '0;
                addr_gen_wr_val         <= 1'b0;
           end else begin //keep in reset if not busy
                addr_gen_wr_busy        <= 1'b0;
                addr_gen_wr_lin_i       <= '0;
                addr_gen_wr_lin_lim     <= '0;
                addr_gen_wr_val         <= 1'b0;
                mmem_if_wr_port_mux     <= IDLE;
           end
        end
    end
end

assign addr_gen_wr_last          = addr_gen_wr_val & addr_gen_wr_lin_i == addr_gen_wr_lin_lim-1; //generate last signal
//add result address offset
assign addr_gen_wr_fin_add_op_a  = addr_gen_wr_lin_i;
assign addr_gen_wr_fin_add_op_b  = tens_trans_spec_i.tens_trans_addrs.tens_res_addr;

del_chain //delay the write port mux 
#(
    .IN_WORD_WDT($bits(mmem_if_wr_port_mux)),
    .DEL_CYC_LEN(C_ADD_ADDR_CYC_LEN)
)
addr_gen_wr_mux_del_chain
(
    .clk(clk),
    .rst_n(addr_gen_rst_n),
    .clk_en(addr_gen_wr_clk_en),
    .in_word(mmem_if_wr_port_mux),
    .in_word_val(),
    .in_word_del(addr_gen_wr_mmem_q.cmd_wr_port_mux),
    .in_word_val_del()
);

del_chain //delay chain for the last signal
#(
    .IN_WORD_WDT(1),
    .DEL_CYC_LEN(C_ADD_ADDR_CYC_LEN)
)
addr_gen_wr_mem_last_del_chain
(
    .clk(clk),
    .rst_n(addr_gen_rst_n),
    .clk_en(addr_gen_wr_clk_en),
    .in_word(addr_gen_wr_last),
    .in_word_val(),
    .in_word_del(addr_gen_wr_mmem_q.cmd_wr_data_vect_last),
    .in_word_val_del()
);

add_cell 
#(
    .ADD_ARITH_CFG(C_ADDR_ADD_ARITH_CFG),
    .ADD_IN_CYC_LEN(C_ADD_ADDR_IN_CYC_LEN),
    .ADD_OUT_CYC_LEN(C_ADD_ADDR_OUT_CYC_LEN)
)
addr_gen_wr_fin_add
( 
  .clk(clk),
  .rst_n(addr_gen_rst_n),
  .clk_en(addr_gen_wr_clk_en),
  .add_op_a(addr_gen_wr_fin_add_op_a), 
  .add_op_b(addr_gen_wr_fin_add_op_b),
  .add_op_val(addr_gen_wr_val),
  .add_res(addr_gen_wr_mmem_q.cmd_wr_addr),
  .add_res_val(addr_gen_wr_mmem_q.cmd_wr_en)
);

del_chain //final delay chain for the mmem write command
#(
    .IN_WORD_WDT($bits(addr_gen_wr_mmem_q)),
    .DEL_CYC_LEN(C_ADDR_GEN_WR_MMEM_CMD_CYC_LEN)
)
addr_gen_wr_mem_del_chain
(
    .clk(clk),
    .rst_n(addr_gen_rst_n),
    .clk_en(addr_gen_wr_clk_en),
    .in_word(addr_gen_wr_mmem_q),
    .in_word_val(),
    .in_word_del(addr_gen_wr_mmem),
    .in_word_val_del()
);

always_ff @(posedge clk) begin : addr_gen_perf_cnt_step_reg
    if(!addr_gen_rst_n) begin
        perf_cnt_step_addr_gen <= '0;
    end else begin
        perf_cnt_step_addr_gen[C_PERF_STREAM_C2H_OFFSET] <= addr_gen_rd_busy & tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_STREAM;
        perf_cnt_step_addr_gen[C_PERF_STREAM_H2C_OFFSET] <= addr_gen_wr_busy & tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_STREAM;
    end
end

// synthesis translate_off

//assertions
always @(posedge clk) assert (!(addr_gen_lin_rd_mmem_q.cmd_rd_en & conv_addr_gen_rd_mmem_q.cmd_rd_en) | !rst_n) 
    else $error("Conflict at the linear/convolution indices MUX!");

asrt_conv_rd_mmem_cmd: assert property (@(posedge clk) disable iff (!rst_n) (conv_addr_gen_rd_mmem_q.cmd_rd_en |-> conv_addr_gen_rd_mmem_q.cmd_rd_data_vect_type == TYPE_DATA & (tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_CONV | tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_MAXPOOL))) 
        else $error("Incorrect data type or transformation type at the read command!");

asrt_lin_rd_mmem_cmd: assert property (@(posedge clk) disable iff (!rst_n) (addr_gen_lin_rd_mmem_q.cmd_rd_en |-> !(addr_gen_lin_rd_mmem_q.cmd_rd_data_vect_type == TYPE_DATA & (tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_CONV | tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_MAXPOOL)))) 
        else $error("Incorrect data type or transformation type at the read command!");

// synthesis translate_on

endmodule