`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     main_fsm
// Project Name:    Efficient FPGA CNN implementation
// Description:     Main FSM of the accelerator. Provides the address generation unit with 
//                  tensor transformation information. Starts the exectution of the address 
//                  generation and at the end receives a done signal. Provides enable and clear 
//                  signals based on the executed transformation.
//
//                  Provides step signals to the performance counters module based on the
//                  currently executed transformation. 
//
//                  Interfaces with the register map through read and write channel
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import regmap_pckg::*;
import regmap_reg_pckg::*;
import proc_pipe_pckg::*;
import perf_cnt_pckg::*;

module main_fsm
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    //control
    output logic [C_PERF_CNT_CNT-1:0]           perf_cnt_step_fsm,
    input  logic [C_PERF_CNT_CNT-1:0]           perf_cnt_step_addr_gen,
    output tens_trans_spec_t                    tens_trans_spec,
    regmap_rd_if.requester                      main_fsm_regmap_rd_if,
    output logic [C_TENS_TRANS_SEQ_CNT_WDT-1:0] tens_trans_seq_cnt,
    input  logic [C_TENS_TRANS_SEQ_CNT_WDT-1:0] tens_trans_seq_lim,
    block_ctrl_if.master                        addr_gen_s_ctrl_if,
    block_ctrl_if.slave                         main_fsm_s_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 sys_arr_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 batch_norm_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 nlin_f_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 maxpool_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 addr_gen_rd_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 addr_gen_wr_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 mmem_if_rd_cmd_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 mmem_if_wr_cmd_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 mmem_if_rd_data_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 mmem_if_wr_data_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 m_axis_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 s_axis_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 mmem_if_ext_out_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_ctrl                 mmem_if_ext_in_pipe_ctrl_if
);

typedef enum 
{
    MAIN_FSM_IDLE,              //FSM is not doing anything, waiting for a start signal from regmap
    MAIN_FSM_RD_SPEC,           //FSM is reading the transformation spec from the regmap
    MAIN_FSM_CLEAR,             //FSM clears all the corresponding blocks
    MAIN_FSM_TRANS_BUSY,        //transformation in process
    MAIN_FSM_TRANS_DONE,        //transformation is done
    MAIN_FSM_TRANS_ALL_DONE     //the whole sequence of transformations is done
} 
main_fsm_state_t;

main_fsm_state_t main_fsm_curr_state;
main_fsm_state_t main_fsm_next_state;

logic tens_trans_spec_rd_done;
logic [C_TENS_TRANS_SEQ_CNT_WDT-1:0] tens_trans_seq_cnt_i;
logic [C_TENS_TRANS_SEQ_CNT_WDT-1:0] tens_trans_seq_lim_i;
logic main_fsm_rd_spec_start;
logic addr_gen_s_ctrl_if_start_q;
logic [C_PIPE_IF_CLEAR_EN_WDT-1:0] pipe_ctrl_if_clear_en_packed_q;
logic [C_PIPE_IF_CLEAR_EN_WDT-1:0] pipe_ctrl_if_clear_en_packed;
logic maxpool_pipe_ctrl_if_en           ;
logic maxpool_pipe_ctrl_if_clear        ;
logic sys_arr_pipe_ctrl_if_en           ;
logic sys_arr_pipe_ctrl_if_clear        ;
logic batch_norm_pipe_ctrl_if_en        ;
logic batch_norm_pipe_ctrl_if_clear     ;
logic nlin_f_pipe_ctrl_if_en            ;
logic nlin_f_pipe_ctrl_if_clear         ;
logic addr_gen_rd_pipe_ctrl_if_en       ;
logic addr_gen_rd_pipe_ctrl_if_clear    ;
logic addr_gen_wr_pipe_ctrl_if_en       ;
logic addr_gen_wr_pipe_ctrl_if_clear    ;
logic mmem_if_rd_cmd_pipe_ctrl_if_en    ;
logic mmem_if_rd_cmd_pipe_ctrl_if_clear ;    
logic mmem_if_wr_cmd_pipe_ctrl_if_en    ;
logic mmem_if_wr_cmd_pipe_ctrl_if_clear ;
logic mmem_if_rd_data_pipe_ctrl_if_en   ;
logic mmem_if_rd_data_pipe_ctrl_if_clear;
logic mmem_if_wr_data_pipe_ctrl_if_en   ;
logic mmem_if_wr_data_pipe_ctrl_if_clear;
logic m_axis_pipe_ctrl_if_en            ;
logic m_axis_pipe_ctrl_if_clear         ;
logic s_axis_pipe_ctrl_if_en            ;
logic s_axis_pipe_ctrl_if_clear         ;
logic mmem_if_ext_out_pipe_ctrl_if_en   ;
logic mmem_if_ext_out_pipe_ctrl_if_clear;
logic mmem_if_ext_in_pipe_ctrl_if_en    ;
logic mmem_if_ext_in_pipe_ctrl_if_clear ;


//state register
always_ff @(posedge clk) begin : main_fsm_state_reg
    if(!rst_n) begin
        main_fsm_curr_state <= MAIN_FSM_IDLE; 
    end else begin
        main_fsm_curr_state <= main_fsm_next_state;
    end
end

always_comb begin : main_fsm_next_state_proc
    main_fsm_next_state = main_fsm_curr_state;
    casez (main_fsm_curr_state)
        MAIN_FSM_IDLE            : main_fsm_next_state = main_fsm_s_ctrl_if.start ? MAIN_FSM_RD_SPEC : MAIN_FSM_IDLE; //start signal came from regmap control register
        MAIN_FSM_RD_SPEC         : main_fsm_next_state = tens_trans_spec_rd_done  ? MAIN_FSM_CLEAR   : MAIN_FSM_RD_SPEC; //start reading the transformation spec from the regmap
        MAIN_FSM_CLEAR           : main_fsm_next_state = MAIN_FSM_TRANS_BUSY; //clear all the blocks
        MAIN_FSM_TRANS_BUSY      : main_fsm_next_state = addr_gen_s_ctrl_if.done  ? MAIN_FSM_TRANS_DONE : MAIN_FSM_TRANS_BUSY; //transformation in progress
        MAIN_FSM_TRANS_DONE      : main_fsm_next_state = tens_trans_seq_cnt_i < tens_trans_seq_lim_i ? MAIN_FSM_RD_SPEC : MAIN_FSM_TRANS_ALL_DONE; //once all transformations are done, return to IDLE state
        MAIN_FSM_TRANS_ALL_DONE  : main_fsm_next_state = MAIN_FSM_IDLE;
        default                  : main_fsm_next_state = main_fsm_curr_state;
    endcase
end

always_ff @(posedge clk) begin : main_fsm_rd_spec_start_reg
    if(!rst_n) begin
        main_fsm_rd_spec_start <= 1'b0;
    end else begin
        main_fsm_rd_spec_start <= main_fsm_curr_state != MAIN_FSM_RD_SPEC & main_fsm_next_state == MAIN_FSM_RD_SPEC;
    end
end

logic main_fsm_s_ctrl_if_done_i; 

//forward the info to the regmap
always_ff @(posedge clk) begin : main_fsm_s_ctrl_if_done_reg
    if(!rst_n) begin
        main_fsm_s_ctrl_if_done_i <= 1'b0;
        main_fsm_s_ctrl_if.done   <= 1'b0;
    end else begin
        main_fsm_s_ctrl_if_done_i <= main_fsm_curr_state == MAIN_FSM_TRANS_ALL_DONE;
        main_fsm_s_ctrl_if.done <= main_fsm_s_ctrl_if_done_i;
    end
end

//transformation sequence counter
always_ff @(posedge clk) begin : tens_trans_seq_cnt_proc
    if(!rst_n) begin
        tens_trans_seq_cnt_i <= '0;
        tens_trans_seq_lim_i <= '0; 
        tens_trans_seq_cnt   <= '0;
    end else begin
        if(main_fsm_curr_state == MAIN_FSM_TRANS_ALL_DONE)
            tens_trans_seq_cnt_i <= '0;
        else if(addr_gen_s_ctrl_if.done)
            tens_trans_seq_cnt_i <= tens_trans_seq_cnt_i + 1;
        tens_trans_seq_lim_i <= tens_trans_seq_lim;
        tens_trans_seq_cnt   <= tens_trans_seq_cnt_i;
    end
end

//process for setting the enables and clear of different proc. pipeline blocks
always_ff @(posedge clk) begin : en_clear_pipe_blocks_proc
    if(!rst_n) begin
        maxpool_pipe_ctrl_if_en             <= 1'b0;
        maxpool_pipe_ctrl_if_clear          <= 1'b0;
        sys_arr_pipe_ctrl_if_en             <= 1'b0;
        sys_arr_pipe_ctrl_if_clear          <= 1'b0;
        batch_norm_pipe_ctrl_if_en          <= 1'b0;
        batch_norm_pipe_ctrl_if_clear       <= 1'b0;
        nlin_f_pipe_ctrl_if_en              <= 1'b0;
        nlin_f_pipe_ctrl_if_clear           <= 1'b0;
        addr_gen_rd_pipe_ctrl_if_en         <= 1'b0;
        addr_gen_rd_pipe_ctrl_if_clear      <= 1'b0;
        addr_gen_wr_pipe_ctrl_if_en         <= 1'b0;
        addr_gen_wr_pipe_ctrl_if_clear      <= 1'b0;
        mmem_if_rd_cmd_pipe_ctrl_if_en      <= 1'b0;
        mmem_if_rd_cmd_pipe_ctrl_if_clear   <= 1'b0;    
        mmem_if_wr_cmd_pipe_ctrl_if_en      <= 1'b0;
        mmem_if_wr_cmd_pipe_ctrl_if_clear   <= 1'b0;
        mmem_if_rd_data_pipe_ctrl_if_en     <= 1'b0;
        mmem_if_rd_data_pipe_ctrl_if_clear  <= 1'b0;
        mmem_if_wr_data_pipe_ctrl_if_en     <= 1'b0;
        mmem_if_wr_data_pipe_ctrl_if_clear  <= 1'b0;
        m_axis_pipe_ctrl_if_en              <= 1'b0;
        m_axis_pipe_ctrl_if_clear           <= 1'b0;
        s_axis_pipe_ctrl_if_en              <= 1'b0;
        s_axis_pipe_ctrl_if_clear           <= 1'b0;
        mmem_if_ext_out_pipe_ctrl_if_en     <= 1'b0;
        mmem_if_ext_out_pipe_ctrl_if_clear  <= 1'b0;
        mmem_if_ext_in_pipe_ctrl_if_en      <= 1'b0;
        mmem_if_ext_in_pipe_ctrl_if_clear   <= 1'b0;
    end else begin
        //default assignment - everything is turned off
        maxpool_pipe_ctrl_if_en             <= 1'b0;
        maxpool_pipe_ctrl_if_clear          <= 1'b0;
        sys_arr_pipe_ctrl_if_en             <= 1'b0;
        sys_arr_pipe_ctrl_if_clear          <= 1'b0;
        batch_norm_pipe_ctrl_if_en          <= 1'b0;
        batch_norm_pipe_ctrl_if_clear       <= 1'b0;
        nlin_f_pipe_ctrl_if_en              <= 1'b0;
        nlin_f_pipe_ctrl_if_clear           <= 1'b0;
        addr_gen_rd_pipe_ctrl_if_en         <= 1'b0;
        addr_gen_rd_pipe_ctrl_if_clear      <= 1'b0;
        addr_gen_wr_pipe_ctrl_if_en         <= 1'b0;
        addr_gen_wr_pipe_ctrl_if_clear      <= 1'b0;
        mmem_if_rd_cmd_pipe_ctrl_if_en      <= 1'b0;
        mmem_if_rd_cmd_pipe_ctrl_if_clear   <= 1'b0;
        mmem_if_wr_cmd_pipe_ctrl_if_en      <= 1'b0;
        mmem_if_wr_cmd_pipe_ctrl_if_clear   <= 1'b0;
        mmem_if_rd_data_pipe_ctrl_if_en     <= 1'b0;
        mmem_if_rd_data_pipe_ctrl_if_clear  <= 1'b0;
        mmem_if_wr_data_pipe_ctrl_if_en     <= 1'b0;
        mmem_if_wr_data_pipe_ctrl_if_clear  <= 1'b0;
        m_axis_pipe_ctrl_if_en              <= 1'b0;
        m_axis_pipe_ctrl_if_clear           <= 1'b0;
        s_axis_pipe_ctrl_if_en              <= 1'b0;
        s_axis_pipe_ctrl_if_clear           <= 1'b0;
        mmem_if_ext_out_pipe_ctrl_if_en     <= 1'b0;
        mmem_if_ext_out_pipe_ctrl_if_clear  <= 1'b0;
        mmem_if_ext_in_pipe_ctrl_if_en      <= 1'b0;
        mmem_if_ext_in_pipe_ctrl_if_clear   <= 1'b0;
        //clear signals
        casez (main_fsm_curr_state)
            MAIN_FSM_CLEAR : begin
                maxpool_pipe_ctrl_if_clear          <= 1'b1;
                sys_arr_pipe_ctrl_if_clear          <= 1'b1;
                batch_norm_pipe_ctrl_if_clear       <= 1'b1;
                nlin_f_pipe_ctrl_if_clear           <= 1'b1;
                addr_gen_rd_pipe_ctrl_if_clear      <= 1'b1;
                addr_gen_wr_pipe_ctrl_if_clear      <= 1'b1;
                mmem_if_rd_cmd_pipe_ctrl_if_clear   <= 1'b1;
                mmem_if_wr_cmd_pipe_ctrl_if_clear   <= 1'b1;
                mmem_if_rd_data_pipe_ctrl_if_clear  <= 1'b1;
                mmem_if_wr_data_pipe_ctrl_if_clear  <= 1'b1;
                m_axis_pipe_ctrl_if_clear           <= 1'b1;
                s_axis_pipe_ctrl_if_clear           <= 1'b1;
                mmem_if_ext_out_pipe_ctrl_if_clear  <= 1'b1;
                mmem_if_ext_in_pipe_ctrl_if_clear   <= 1'b1;
            end
            MAIN_FSM_TRANS_BUSY : begin
                if(tens_trans_spec_i.tens_trans_cfg.tens_trans_type != TRANS_STREAM) begin
                    maxpool_pipe_ctrl_if_en             <= 1'b1;
                    sys_arr_pipe_ctrl_if_en             <= 1'b1;
                    batch_norm_pipe_ctrl_if_en          <= 1'b1;
                    nlin_f_pipe_ctrl_if_en              <= 1'b1;
                    addr_gen_rd_pipe_ctrl_if_en         <= 1'b1;
                    addr_gen_wr_pipe_ctrl_if_en         <= 1'b1;
                    mmem_if_rd_cmd_pipe_ctrl_if_en      <= 1'b1;
                    mmem_if_wr_cmd_pipe_ctrl_if_en      <= 1'b1;
                    mmem_if_rd_data_pipe_ctrl_if_en     <= 1'b1;
                    mmem_if_wr_data_pipe_ctrl_if_en     <= 1'b1;
                end else begin
                    addr_gen_rd_pipe_ctrl_if_en         <= 1'b1;
                    addr_gen_wr_pipe_ctrl_if_en         <= 1'b1;
                    mmem_if_rd_cmd_pipe_ctrl_if_en      <= 1'b1;
                    mmem_if_wr_cmd_pipe_ctrl_if_en      <= 1'b1;
                    m_axis_pipe_ctrl_if_en              <= 1'b1;
                    s_axis_pipe_ctrl_if_en              <= 1'b1;
                    mmem_if_ext_out_pipe_ctrl_if_en     <= 1'b1;
                    mmem_if_ext_in_pipe_ctrl_if_en      <= 1'b1;
                end
            end
        endcase
    end
end

genvar i;
generate
    for(i = 0; i < C_PIPE_IF_CLEAR_EN_WDT; i++) begin
        del_chain
        #(
            .IN_WORD_WDT (1), 
            .DEL_CYC_LEN (C_PIPE_IF_CLEAR_EN_DEL_CYC_LEN)
        )
        pipe_ctrl_if_clear_en_del_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(1'b1),
            .in_word(pipe_ctrl_if_clear_en_packed_q[i]), 
            .in_word_val(),
            .in_word_del(pipe_ctrl_if_clear_en_packed[i]),
            .in_word_val_del()
        );

    end
endgenerate

always_comb begin : pipe_if_en_clear_pack_unpack
    pipe_ctrl_if_clear_en_packed_q = 
    {
        maxpool_pipe_ctrl_if_en           ,
        maxpool_pipe_ctrl_if_clear        ,
        sys_arr_pipe_ctrl_if_en           ,
        sys_arr_pipe_ctrl_if_clear        ,
        batch_norm_pipe_ctrl_if_en        ,
        batch_norm_pipe_ctrl_if_clear     ,
        nlin_f_pipe_ctrl_if_en            ,
        nlin_f_pipe_ctrl_if_clear         ,
        addr_gen_rd_pipe_ctrl_if_en       ,
        addr_gen_rd_pipe_ctrl_if_clear    ,
        addr_gen_wr_pipe_ctrl_if_en       ,
        addr_gen_wr_pipe_ctrl_if_clear    ,
        mmem_if_rd_cmd_pipe_ctrl_if_en    ,
        mmem_if_rd_cmd_pipe_ctrl_if_clear ,
        mmem_if_wr_cmd_pipe_ctrl_if_en    ,
        mmem_if_wr_cmd_pipe_ctrl_if_clear ,
        mmem_if_rd_data_pipe_ctrl_if_en   ,
        mmem_if_rd_data_pipe_ctrl_if_clear,
        mmem_if_wr_data_pipe_ctrl_if_en   ,
        mmem_if_wr_data_pipe_ctrl_if_clear,
        m_axis_pipe_ctrl_if_en            ,
        m_axis_pipe_ctrl_if_clear         ,
        s_axis_pipe_ctrl_if_en            ,
        s_axis_pipe_ctrl_if_clear         ,
        mmem_if_ext_out_pipe_ctrl_if_en   ,
        mmem_if_ext_out_pipe_ctrl_if_clear,
        mmem_if_ext_in_pipe_ctrl_if_en    ,
        mmem_if_ext_in_pipe_ctrl_if_clear
    };
    
    maxpool_pipe_ctrl_if.en            = pipe_ctrl_if_clear_en_packed[27] ;
    maxpool_pipe_ctrl_if.clear         = pipe_ctrl_if_clear_en_packed[26] ;
    sys_arr_pipe_ctrl_if.en            = pipe_ctrl_if_clear_en_packed[25] ;
    sys_arr_pipe_ctrl_if.clear         = pipe_ctrl_if_clear_en_packed[24] ;
    batch_norm_pipe_ctrl_if.en         = pipe_ctrl_if_clear_en_packed[23] ;
    batch_norm_pipe_ctrl_if.clear      = pipe_ctrl_if_clear_en_packed[22] ;
    nlin_f_pipe_ctrl_if.en             = pipe_ctrl_if_clear_en_packed[21] ;
    nlin_f_pipe_ctrl_if.clear          = pipe_ctrl_if_clear_en_packed[20] ;
    addr_gen_rd_pipe_ctrl_if.en        = pipe_ctrl_if_clear_en_packed[19] ;
    addr_gen_rd_pipe_ctrl_if.clear     = pipe_ctrl_if_clear_en_packed[18] ;
    addr_gen_wr_pipe_ctrl_if.en        = pipe_ctrl_if_clear_en_packed[17] ;
    addr_gen_wr_pipe_ctrl_if.clear     = pipe_ctrl_if_clear_en_packed[16] ;
    mmem_if_rd_cmd_pipe_ctrl_if.en     = pipe_ctrl_if_clear_en_packed[15];
    mmem_if_rd_cmd_pipe_ctrl_if.clear  = pipe_ctrl_if_clear_en_packed[14];
    mmem_if_wr_cmd_pipe_ctrl_if.en     = pipe_ctrl_if_clear_en_packed[13];
    mmem_if_wr_cmd_pipe_ctrl_if.clear  = pipe_ctrl_if_clear_en_packed[12];
    mmem_if_rd_data_pipe_ctrl_if.en    = pipe_ctrl_if_clear_en_packed[11];
    mmem_if_rd_data_pipe_ctrl_if.clear = pipe_ctrl_if_clear_en_packed[10];
    mmem_if_wr_data_pipe_ctrl_if.en    = pipe_ctrl_if_clear_en_packed[9];
    mmem_if_wr_data_pipe_ctrl_if.clear = pipe_ctrl_if_clear_en_packed[8];
    m_axis_pipe_ctrl_if.en             = pipe_ctrl_if_clear_en_packed[7];
    m_axis_pipe_ctrl_if.clear          = pipe_ctrl_if_clear_en_packed[6];
    s_axis_pipe_ctrl_if.en             = pipe_ctrl_if_clear_en_packed[5];
    s_axis_pipe_ctrl_if.clear          = pipe_ctrl_if_clear_en_packed[4];
    mmem_if_ext_out_pipe_ctrl_if.en    = pipe_ctrl_if_clear_en_packed[3];
    mmem_if_ext_out_pipe_ctrl_if.clear = pipe_ctrl_if_clear_en_packed[2];
    mmem_if_ext_in_pipe_ctrl_if.en     = pipe_ctrl_if_clear_en_packed[1];
    mmem_if_ext_in_pipe_ctrl_if.clear  = pipe_ctrl_if_clear_en_packed[0];
end

//process for setting the perf counter step signals
always_ff @(posedge clk) begin : perf_cnt_step_proc
    if(!rst_n) begin
        perf_cnt_step_fsm <= '0; 
    end else begin
        perf_cnt_step_fsm <= '0;

        perf_cnt_step_fsm[C_PERF_RUN_OFFSET] <= 1'b1;
        if(main_fsm_curr_state == MAIN_FSM_TRANS_BUSY) begin
            if(tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_STREAM) begin
                perf_cnt_step_fsm[C_PERF_STREAM_C2H_OFFSET] <= perf_cnt_step_addr_gen[C_PERF_STREAM_C2H_OFFSET];
                perf_cnt_step_fsm[C_PERF_STREAM_H2C_OFFSET] <= perf_cnt_step_addr_gen[C_PERF_STREAM_H2C_OFFSET];
            end else begin
                perf_cnt_step_fsm[C_PERF_COMP_OFFSET] <= 1'b1;
                perf_cnt_step_fsm[C_PERF_CACHE_STALL_OFFSET] <= 1'b0; //TODO: reserved for future cache implementation
            end
        end
    end
end

tens_trans_spec_t      tens_trans_spec_i;
logic [C_REGMAP_ADDR_WDT-1:0] tens_trans_spec_offset; 
logic [C_REGMAP_ADDR_WDT-1:0] tens_trans_spec_offset_q;
logic main_fsm_regmap_rd_if_rd_en_i;  
logic [C_S_AXI_ADDR_WDT-1:0] main_fsm_regmap_rd_if_rd_addr_i;

always_ff @(posedge clk) begin : tens_trans_seq_rd_proc //process for doing the regmap read
    if(!rst_n) begin
        main_fsm_regmap_rd_if_rd_en_i         <= 1'b0;
        main_fsm_regmap_rd_if_rd_addr_i       <= C_TENS_TRANS_CFG_REG_ADDR;
        tens_trans_spec_i                   <= '0; 
        tens_trans_spec                     <= '0;
        tens_trans_spec_offset              <= '0;
    end else begin
        if(main_fsm_curr_state == MAIN_FSM_RD_SPEC) begin //start reading
            casez (tens_trans_spec_offset)
                0 : begin //start of read, reset current spec
                    tens_trans_spec_i        <= '0;
                end
                C_TENS_TRANS_CFG_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_cfg.tens_trans_type        <= tens_trans_type_t'(main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_LSB   +: C_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_WIDTH]);
                        tens_trans_spec_i.tens_trans_cfg.nlin_f_type            <= nlin_f_type_t'(main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CFG_REG_NLIN_F_TYPE_LSB       +: C_TENS_TRANS_CFG_REG_NLIN_F_TYPE_WIDTH]); 
                        tens_trans_spec_i.tens_trans_cfg.batch_norm_en          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CFG_REG_BATCH_NORM_EN_LSB     +: C_TENS_TRANS_CFG_REG_BATCH_NORM_EN_WIDTH]; 
                        tens_trans_spec_i.tens_trans_cfg.repl_bias              <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CFG_REG_REPL_BIAS_LSB         +: C_TENS_TRANS_CFG_REG_REPL_BIAS_WIDTH]; 
                        tens_trans_spec_i.tens_trans_cfg.bias_en                <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CFG_REG_BIAS_EN_LSB           +: C_TENS_TRANS_CFG_REG_BIAS_EN_WIDTH]; 
                    end
                end
                C_TENS_TRANS_CONV_CFG_REG_ADDR: begin
                    tens_trans_spec_i.tens_trans_cfg.conv_cfg.conv_stride_0   <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_LSB       +: C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_WIDTH]; 
                    tens_trans_spec_i.tens_trans_cfg.conv_cfg.conv_stride_1   <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_LSB       +: C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_WIDTH]; 
                    tens_trans_spec_i.tens_trans_cfg.conv_cfg.conv_padding_0  <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_LSB      +: C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_WIDTH]; 
                    tens_trans_spec_i.tens_trans_cfg.conv_cfg.conv_padding_1  <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_LSB      +: C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_WIDTH]; 
                end
                C_TENS_TRANS_ADDR_SRC_A_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_addrs.tens_src_a_addr        <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_LSB   +: C_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_WIDTH];
                    end
                end
                C_TENS_TRANS_ADDR_SRC_B_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_addrs.tens_src_b_addr        <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_LSB   +: C_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_WIDTH];
                    end
                end
                C_TENS_TRANS_ADDR_BATCH_NORM_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_addrs.tens_batch_norm_addr   <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_LSB   +: C_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_WIDTH];
                    end
                end
                C_TENS_TRANS_ADDR_BIAS_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_addrs.tens_bias_addr         <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_LSB   +: C_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_WIDTH];
                    end
                end
                C_TENS_TRANS_ADDR_RES_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_addrs.tens_res_addr          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_LSB   +: C_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_WIDTH];
                    end
                end
                C_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_0_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_LSB   +: C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_WIDTH];
                        tens_trans_spec_i.tens_trans_lin_dims.tens_src_a_dims.tens_1_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_LSB   +: C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_WIDTH];
                    end
                end
                C_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_0_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_LSB   +: C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_WIDTH];
                        tens_trans_spec_i.tens_trans_lin_dims.tens_src_b_dims.tens_1_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_LSB   +: C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_WIDTH];
                    end
                end
                C_TENS_TRANS_LIN_DIMS_RES_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_lin_dims.tens_res_dims.tens_0_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_LSB   +: C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_WIDTH];
                        tens_trans_spec_i.tens_trans_lin_dims.tens_res_dims.tens_1_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_LSB   +: C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_WIDTH];
                    end
                end
                C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_conv_dims.tens_src_a_dims.tens_0_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_WIDTH];
                        tens_trans_spec_i.tens_trans_conv_dims.tens_src_a_dims.tens_1_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_WIDTH];
                    end
                end
                C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_conv_dims.tens_src_a_dims.tens_2_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_WIDTH];
                        tens_trans_spec_i.tens_trans_conv_dims.tens_src_a_dims.tens_3_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_WIDTH];
                    end
                end
                C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_conv_dims.tens_src_b_dims.tens_0_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_WIDTH];
                        tens_trans_spec_i.tens_trans_conv_dims.tens_src_b_dims.tens_1_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_WIDTH];
                    end
                end
                C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_conv_dims.tens_src_b_dims.tens_2_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_WIDTH];
                        tens_trans_spec_i.tens_trans_conv_dims.tens_src_b_dims.tens_3_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_WIDTH];
                    end
                end
                C_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_conv_dims.tens_res_dims.tens_0_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_WIDTH];
                        tens_trans_spec_i.tens_trans_conv_dims.tens_res_dims.tens_1_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_WIDTH];
                    end
                end
                C_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR : begin
                    if(main_fsm_regmap_rd_if.rd_val) begin
                        tens_trans_spec_i.tens_trans_conv_dims.tens_res_dims.tens_2_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_WIDTH];
                        tens_trans_spec_i.tens_trans_conv_dims.tens_res_dims.tens_3_dim          <= main_fsm_regmap_rd_if.rd_data[C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_LSB   +: C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_WIDTH];
                    end
                end
                default: begin
                    tens_trans_spec_i <= tens_trans_spec_i; //no change
                end
            endcase

            tens_trans_spec_offset          <= main_fsm_rd_spec_start ? C_TENS_TRANS_CFG_REG_ADDR : tens_trans_spec_offset_q;
            main_fsm_regmap_rd_if_rd_addr_i   <= main_fsm_regmap_rd_if.rd_val ? main_fsm_regmap_rd_if_rd_addr_i + 4 : main_fsm_regmap_rd_if_rd_addr_i; //increment on each succesful read
            if(!tens_trans_spec_rd_done) begin
                main_fsm_regmap_rd_if_rd_en_i     <= tens_trans_spec_offset != tens_trans_spec_offset_q | main_fsm_rd_spec_start; //issue read if offset is set to change    
            end else begin
                main_fsm_regmap_rd_if_rd_en_i     <= 1'b0;    
            end
        end else if(main_fsm_curr_state == MAIN_FSM_TRANS_ALL_DONE) begin//sequence is done, reset all
            main_fsm_regmap_rd_if_rd_en_i   <= 1'b0;
            main_fsm_regmap_rd_if_rd_addr_i   <= C_TENS_TRANS_CFG_REG_ADDR;
            tens_trans_spec_i               <= '0; 
            tens_trans_spec_offset          <= '0;
        end 
        tens_trans_spec                 <= tens_trans_spec_i;
    end
end

always_comb begin : tens_trans_spec_offset_next
    tens_trans_spec_offset_q = tens_trans_spec_offset;
        
    if(main_fsm_regmap_rd_if.rd_val) //new valid word, advance to next word
        if(tens_trans_spec_offset == 0) 
            tens_trans_spec_offset_q = C_TENS_TRANS_CFG_REG_ADDR; //start of read, reset offset
        else if(tens_trans_spec_offset == C_TENS_TRANS_LIN_DIMS_RES_REG_ADDR & !(tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_CONV | tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_MAXPOOL))
            tens_trans_spec_offset_q = 0; //end of specification (non convolution case)
        else if(tens_trans_spec_offset == C_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR & (tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_CONV | tens_trans_spec_i.tens_trans_cfg.tens_trans_type == TRANS_MAXPOOL))
            tens_trans_spec_offset_q = 0; //end of specification (convolution case)
        else if(tens_trans_spec_offset >= C_REGMAP_RAM_START_ADDR + (C_REGMAP_TENS_TRANS_SPEC_WORD_CNT << 4))
            tens_trans_spec_offset_q = 0; //end of specification (in case something goes wrong)
        else
            tens_trans_spec_offset_q = tens_trans_spec_offset + 4;

    tens_trans_spec_rd_done = tens_trans_spec_offset_q == 0 & tens_trans_spec_offset != 0; //send done signal to FSM
end

assign addr_gen_s_ctrl_if_start_q = main_fsm_curr_state == MAIN_FSM_CLEAR; //start the address generation after the clear state

del_chain
#(
    .IN_WORD_WDT (1), 
    .DEL_CYC_LEN (C_ADDR_GEN_S_START_CYC_LEN)
)
addr_gen_s_start_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(1'b1),
    .in_word(addr_gen_s_ctrl_if_start_q), 
    .in_word_val(),
    .in_word_del(addr_gen_s_ctrl_if.start),
    .in_word_val_del()
);

del_chain
#(
    .IN_WORD_WDT ($bits(main_fsm_regmap_rd_if_rd_addr_i)), 
    .DEL_CYC_LEN (C_MAIN_FSM_REGMAP_RD_IF_CYC_LEN)
)
main_fsm_regmap_rd_if_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(1'b1),
    .in_word(main_fsm_regmap_rd_if_rd_addr_i), 
    .in_word_val(main_fsm_regmap_rd_if_rd_en_i),
    .in_word_del(main_fsm_regmap_rd_if.rd_addr),
    .in_word_val_del(main_fsm_regmap_rd_if.rd_en)
);

// synthesis translate_off

//assertions
assert property (@(posedge clk) disable iff (!rst_n) ($changed(tens_trans_spec_offset) |-> tens_trans_spec_offset == $past(tens_trans_spec_offset, 1) + 4 | tens_trans_spec_offset == 0 | $past(tens_trans_spec_offset, 1) == 0)) else $error("The word offset within tens. trans. spec. shall only increment by 4 or be set to zero!");
assert property (@(posedge clk) disable iff (!rst_n) ($changed(main_fsm_regmap_rd_if_rd_addr_i) & main_fsm_curr_state == MAIN_FSM_RD_SPEC |-> main_fsm_regmap_rd_if_rd_addr_i == $past(main_fsm_regmap_rd_if_rd_addr_i, 1) + 4 | main_fsm_regmap_rd_if_rd_addr_i == C_TENS_TRANS_CFG_REG_ADDR)) else $error("The read address shall only increment by 4 or be set to initial position when reading the specification!");


// synthesis translate_on

endmodule