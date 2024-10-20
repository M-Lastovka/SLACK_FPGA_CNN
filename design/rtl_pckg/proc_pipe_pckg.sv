`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     proc_pipe_pckg
// Project Name:    Efficient FPGA CNN implementation
// Description:     package for the processing pipeline
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

interface proc_pipe_ctrl_if; //backpressure interface for the blocks in the processing pipeline
logic stall;
logic step;
logic en;
logic clear;

modport proc_block
(
    output stall,
    input step,
    input en,
    input clear
);

modport proc_prod
(
    input stall,
    output step,
    input  en,
    input  clear
);

modport proc_ctrl
(
    input stall,
    input step,
    output en,
    output clear
);
endinterface

interface block_ctrl_if; //simple block control interface
logic start;
logic done;

modport master
(
    output start,
    input  done
);

modport slave
(
    input  start,
    output done
);
endinterface

package proc_pipe_pckg;
import arith_pckg::*;
import regmap_pckg::*;
import tb_pckg::*;

parameter C_BPRESS_FIFO_DEPTH = 2**3;
parameter C_PIPE_IF_CLEAR_EN_WDT = 28;
parameter C_PIPE_IF_CLEAR_EN_DEL_CYC_LEN = 3; //delay of clear/en signals

//-------------------------------------------------------------
//processing pipeline params-----------------------------------
//-------------------------------------------------------------

parameter C_VECT_SIZE = 5; //SIMD vector size - i.e. how many data words fit into a vector
parameter C_VECT_SIZE_CLOG2 = $clog2(C_VECT_SIZE);
parameter C_VECT_WORD_WDT = C_VECT_SIZE*C_ARITH_WORD_LEN; //width of the SIMD vector data, stored in memory
parameter C_SYS_ARR_SIZE = C_VECT_SIZE;

parameter C_PIPE_DATA_TYPE_WDT = 3;

typedef logic[C_PIPE_DATA_TYPE_WDT-1:0] pipe_data_type_t;
parameter pipe_data_type_t TYPE_DATA = 0;
parameter pipe_data_type_t TYPE_STAT_WEIGHT = 1;
parameter pipe_data_type_t TYPE_ACC_BIAS = 2;
parameter pipe_data_type_t TYPE_BATCH_NORM_PARAM = 3;

typedef struct packed 
{
    logic [C_ARITH_WORD_LEN-1:0]            data_word;
    logic                                   data_val;
    logic                                   data_last;
    pipe_data_type_t                        data_type;
} pipe_data_t; //data type defining vector of data as it is flowing through the processing pipeline 

typedef struct packed 
{
    logic [C_VECT_SIZE-1:0][C_ARITH_WORD_LEN-1:0] data_vect_words;
    logic              data_vect_val;
    logic              data_vect_last;
    pipe_data_type_t   data_vect_type;
} pipe_data_vect_t; //data type defining vector of data as it is flowing through the processing pipeline 

parameter C_PIPE_DATA_WDT = C_ARITH_WORD_LEN + C_PIPE_DATA_TYPE_WDT + 2;
parameter pipe_data_vect_t C_PIPE_DATA_VECT_RST_VAL = '{data_vect_words:'0, data_vect_val:1'b0, data_vect_last:1'b0, data_vect_type:'0};
parameter pipe_data_t      C_PIPE_DATA_RST_VAL = '0;
parameter C_PIPE_DATA_VECT_WDT = C_VECT_WORD_WDT + C_PIPE_DATA_TYPE_WDT + 2;

parameter C_SYS_ARR_CELL_FORW_CYC_LEN = 2;
parameter C_SYS_ARR_CELL_MULT_CYC_LEN = 1;

parameter C_ADD_TREE_OP_CNT = C_VECT_SIZE;
parameter C_ADD_TREE_LVL_DEL_CYC_LEN = 1;
parameter C_ADD_TREE_DEL_CYC_LEN = (C_ADD_TREE_LVL_DEL_CYC_LEN + C_ADD_FXP_CYC_LEN)*$clog2(C_ADD_TREE_OP_CNT);

parameter C_SYS_ARR_IN_DEL_CYC_LEN  = 1;
parameter C_SYS_ARR_OUT_DEL_CYC_LEN = 1;

//systolic array accumulator params
parameter C_SYS_ARR_ACC_MEM_PIPE_IN_CNT = 1;
parameter C_SYS_ARR_ACC_MEM_PIPE_OUT_CNT = 1;
parameter C_SYS_ARR_ACC_ADD_CYC_LEN = C_ADD_FXP_CYC_LEN;
parameter C_SYS_ARR_ACC_FETCH_CYC_LEN = C_SYS_ARR_ACC_MEM_PIPE_IN_CNT + C_SYS_ARR_ACC_MEM_PIPE_OUT_CNT + 1;
parameter C_SYS_ARR_ACC_ADDR_WDT = 11;
parameter C_SYS_ARR_ACC_MEM_SIZE = 2**C_SYS_ARR_ACC_ADDR_WDT;

//batch norm params
parameter C_BATCH_NORM_IN_DEL_CYC_LEN   = 1;
parameter C_BATCH_NORM_OUT_DEL_CYC_LEN  = 1;

//non-linear function unit params
parameter C_NLIN_F_IN_DEL_CYC_LEN       = 1;
parameter C_NLIN_F_OUT_DEL_CYC_LEN      = 1;

//-------------------------------------------------------------
//main memory params-------------------------------------------
//-------------------------------------------------------------

typedef enum 
{
    STATIC_BRAM,
    STATIC_URAM,
    CACHE
} mmem_type_t; //main memory configuration type

parameter C_MEM_PORT_MUX_WDT = 3;

typedef logic [C_MEM_PORT_MUX_WDT-1:0] mem_port_mux_t; //controls a memory port (rd or wr) to source/sink data from internal/external source
parameter mem_port_mux_t IDLE = 0;
parameter mem_port_mux_t INTERN = 1;
parameter mem_port_mux_t EXTERN = 2;

parameter mmem_type_t C_MMEM_TYPE = STATIC_URAM;

parameter C_MMEM_ADDR_WDT = 14; //scale of the main memory address space
parameter C_MMEM_DATA_WDT = C_VECT_WORD_WDT;

parameter C_MMEM_PIPE_IN_CNT  = 1;
parameter C_MMEM_PIPE_OUT_CNT = 2;

parameter C_MMEM_MIN_RD_CYC_LEN = C_MMEM_TYPE == STATIC_URAM ? (C_MMEM_PIPE_IN_CNT + C_MMEM_PIPE_OUT_CNT + 4) : (C_MMEM_PIPE_IN_CNT + C_MMEM_PIPE_OUT_CNT + 1); //minimum main memory read latency
parameter C_MMEM_MIN_WR_CYC_LEN = C_MMEM_PIPE_IN_CNT + 1; //minimum main memory write latency

parameter C_TENS_INDEX_WDT = 16;

typedef struct packed
{
    logic cmd_rd_en;
    logic [C_MMEM_ADDR_WDT-1:0] cmd_rd_addr;
    pipe_data_type_t cmd_rd_data_vect_type;
    logic cmd_rd_data_vect_last;
    logic cmd_rd_data_vect_zero_padd;
    logic cmd_rd_data_vect_neg_inf_padd;
    mem_port_mux_t cmd_rd_port_mux;
} mem_cmd_rd_t; //type for the memory command - read

typedef struct packed
{
    logic cmd_wr_en;
    logic [C_MMEM_ADDR_WDT-1:0] cmd_wr_addr;
    logic cmd_wr_data_vect_last;
    mem_port_mux_t cmd_wr_port_mux;
} mem_cmd_wr_t; //type for the memory command - write

//-------------------------------------------------------------
//addr gen unit------------------------------------------------
//-------------------------------------------------------------

parameter C_ADDR_GEN_S_START_CYC_LEN = C_PIPE_IF_CLEAR_EN_DEL_CYC_LEN + 3;
parameter C_MAIN_FSM_REGMAP_RD_IF_CYC_LEN = 2;

parameter C_ADD_ADDR_IN_CYC_LEN = 1;
parameter C_ADD_ADDR_OUT_CYC_LEN = 1;
parameter C_ADD_ADDR_CYC_LEN = C_ADD_ADDR_IN_CYC_LEN + C_ADD_ADDR_OUT_CYC_LEN;
parameter C_MULT_ADDR_IN_CYC_LEN = 2;
parameter C_MULT_ADDR_OUT_CYC_LEN = 1;
parameter C_MULT_ADDR_CYC_LEN = C_MULT_ADDR_IN_CYC_LEN + C_MULT_ADDR_OUT_CYC_LEN;
//arithmetic configuration for computation of main memory addresses
parameter arith_cfg_t C_ADDR_ADD_ARITH_CFG = '{word_wdt:32, fxp_cfg:'{int_wdt:C_MMEM_ADDR_WDT, frac_wdt:0}, arith_type:ADDR_OPT_FPGA, arith_satur:0};
parameter arith_cfg_t C_ADDR_MULT_ARITH_CFG = '{word_wdt:32, fxp_cfg:'{int_wdt:C_MMEM_ADDR_WDT, frac_wdt:0}, arith_type:ADDR_OPT_FPGA, arith_satur:0};

parameter C_ADDR_GEN_RD_COMP_CYC_LEN  = (C_ADD_ADDR_CYC_LEN > C_MULT_ADDR_CYC_LEN ? C_ADD_ADDR_CYC_LEN : C_MULT_ADDR_CYC_LEN) + C_ADD_ADDR_CYC_LEN;
parameter C_ADDR_GEN_RD_MMEM_CMD_CYC_LEN = 1;
parameter C_ADDR_GEN_WR_MMEM_CMD_CYC_LEN = 1;

parameter C_CONV_ADDR_GEN_IN_DEL_CYC_LEN = 1;
parameter C_D_END_TENS_INDEX_WDT  = 2*C_TENS_INDEX_WDT-1;
parameter C_D_QUOT_BITS_PER_CYCLE = 2;
parameter C_INT_DIV_CYC_LEN = C_TENS_INDEX_WDT/C_D_QUOT_BITS_PER_CYCLE + 1;
parameter C_DIV_COL_STRIDE_CYC_LEN = C_MULT_ADDR_CYC_LEN + C_INT_DIV_CYC_LEN;
parameter C_DIV_KERN_ROW_CYC_LEN = 2*C_INT_DIV_CYC_LEN;
parameter C_DIV_COL_STRIDE_REM_DEL_CYC_LEN = C_DIV_KERN_ROW_CYC_LEN - C_DIV_COL_STRIDE_CYC_LEN;
parameter C_CONV_ADDR_GEN_1_STAGE_CYC_LEN = C_DIV_KERN_ROW_CYC_LEN + C_ADD_ADDR_CYC_LEN;
parameter C_CONV_ADDR_GEN_Z_I_CYC_LEN = C_CONV_ADDR_GEN_1_STAGE_CYC_LEN - C_INT_DIV_CYC_LEN;
parameter C_CONV_ADDR_GEN_2_STAGE_CYC_LEN = C_ADD_ADDR_CYC_LEN;
parameter C_MULT_DIV_COL_STRIDE_DEL_CYC_LEN = C_DIV_KERN_ROW_CYC_LEN - (C_INT_DIV_CYC_LEN + 2*C_MULT_ADDR_CYC_LEN);
parameter C_CONV_ADDR_GEN_X_OFFSET_DEL_CYC_LEN = (C_ADD_ADDR_CYC_LEN + 2*C_MULT_ADDR_CYC_LEN) - C_ADD_ADDR_CYC_LEN;
parameter C_CONV_ADDR_GEN_3_STAGE_CYC_LEN = (2*C_ADD_ADDR_CYC_LEN + 2*C_MULT_ADDR_CYC_LEN);
parameter C_CONV_ADDR_GEN_TOT_STAGE_CYC_LEN = C_CONV_ADDR_GEN_1_STAGE_CYC_LEN + C_CONV_ADDR_GEN_2_STAGE_CYC_LEN + C_CONV_ADDR_GEN_3_STAGE_CYC_LEN + C_CONV_ADDR_GEN_IN_DEL_CYC_LEN;
parameter C_CONV_ADDR_GEN_PADD_DEL_CYC_LEN = C_CONV_ADDR_GEN_3_STAGE_CYC_LEN - 1;
parameter C_CONV_ADDR_GEN_LIN_DEL_CYC_LEN = C_CONV_ADDR_GEN_TOT_STAGE_CYC_LEN - C_ADDR_GEN_RD_COMP_CYC_LEN;

//-------------------------------------------------------------
//maxpool unit-------------------------------------------------
//-------------------------------------------------------------

parameter C_MAXPOOL_IN_DEL_CYC_LEN = 1;
parameter C_MAXPOOL_ACC_ADDR_WDT   = 5;
parameter C_MAXPOOL_ACC_SIZE = 2**C_MAXPOOL_ACC_ADDR_WDT;
parameter C_MAXPOOL_ACC_MEM_PIPE_IN_CNT = 0;
parameter C_MAXPOOL_ACC_MEM_PIPE_OUT_CNT = 0;
parameter C_MAXPOOL_ACC_FETCH_CYC_LEN = C_MAXPOOL_ACC_MEM_PIPE_IN_CNT + C_MAXPOOL_ACC_MEM_PIPE_OUT_CNT + 1;
parameter C_MAXPOOL_ACC_COMP_CYC_LEN = C_MAXPOOL_ACC_FETCH_CYC_LEN + 0;
parameter C_MAXPOOL_OUT_DEL_CYC_LEN = 1;

//-------------------------------------------------------------
//tanh unit----------------------------------------------------
//-------------------------------------------------------------

parameter C_TANH_IN_DEL_CYC_LEN = 1;
parameter C_TANH_OUT_DEL_CYC_LEN = 1;
parameter string C_TANH_LUT_PATH = {C_PROJ_PATH, "\\sw\\sim_scripts\\yo\\tanh_lut.txt"};
parameter C_TANH_LUT_MEM_DATA_WDT = C_ARITH_FXP_FRAC_WDT;
parameter C_TANH_DOWN_SA_FACT = 8;
parameter C_TANH_LUT_MEM_ADDR_WDT = 9;
parameter C_TANH_LUT_MEM_SIZE = 2**C_TANH_LUT_MEM_ADDR_WDT;
parameter C_TANH_LIN_END      = real2fxp(0.25);
parameter C_TANH_SAT_START    = real2fxp(4.2);

//-------------------------------------------------------------
//tensor transformation specification params-------------------
//-------------------------------------------------------------

parameter C_TENS_TRANS_TYPE_WDT = $clog2(4);

typedef enum logic [C_TENS_TRANS_TYPE_WDT-1:0] 
{
    TRANS_LIN = 0,        
    TRANS_CONV = 1,
    TRANS_MAXPOOL = 2,
    TRANS_STREAM = 3
} tens_trans_type_t;

parameter C_NLIN_F_TYPE_WDT = $clog2(3);

typedef enum logic [C_NLIN_F_TYPE_WDT-1:0] 
{
    NLIN_F_IDENTITY = 0,        
    NLIN_F_RELU = 1,
    NLIN_F_TANH = 2
} nlin_f_type_t;

parameter C_CONV_PARAM_WDT = 8;

typedef struct packed
{
    logic [C_CONV_PARAM_WDT-1:0] conv_stride_0;
    logic [C_CONV_PARAM_WDT-1:0] conv_stride_1;
    logic [C_CONV_PARAM_WDT-1:0] conv_padding_0;
    logic [C_CONV_PARAM_WDT-1:0] conv_padding_1;
} conv_cfg_t;

typedef struct packed
{
    tens_trans_type_t tens_trans_type;
    nlin_f_type_t     nlin_f_type;
    logic             batch_norm_en;
    logic             repl_bias;
    logic             bias_en;
    conv_cfg_t        conv_cfg;
} tens_trans_cfg_t; //data type defining a tensor transformation configuration - which type of transformation, what non-linearity etc.

parameter C_TENS_DIM_WDT = 16;

typedef struct packed
{
    logic [C_TENS_DIM_WDT-1:0] tens_0_dim;
    logic [C_TENS_DIM_WDT-1:0] tens_1_dim;
    logic [C_TENS_DIM_WDT-1:0] tens_2_dim;
    logic [C_TENS_DIM_WDT-1:0] tens_3_dim;
} tens_trans_dim_t; //data type defining tensor dimensions

typedef struct packed
{
    logic [C_TENS_DIM_WDT-1:0] tens_0_dim;
    logic [C_TENS_DIM_WDT-1:0] tens_1_dim;
} mtx_trans_dim_t; //data type defining matrix dimensions

typedef struct packed
{
    mtx_trans_dim_t tens_src_a_dims;
    mtx_trans_dim_t tens_src_b_dims;
    mtx_trans_dim_t tens_res_dims;
} mtx_trans_dims_t; //data type defining a matrix transformation dimensions - dimensions of the operands and result

typedef struct packed
{
    tens_trans_dim_t tens_src_a_dims;
    tens_trans_dim_t tens_src_b_dims;
    tens_trans_dim_t tens_res_dims;
} tens_trans_dims_t; //data type defining tensor transformation dimensions - dimensions of the operands and result

typedef struct packed
{
    logic [C_MMEM_ADDR_WDT-1:0] tens_src_a_addr;
    logic [C_MMEM_ADDR_WDT-1:0] tens_src_b_addr;
    logic [C_MMEM_ADDR_WDT-1:0] tens_batch_norm_addr;
    logic [C_MMEM_ADDR_WDT-1:0] tens_bias_addr;
    logic [C_MMEM_ADDR_WDT-1:0] tens_res_addr;
} tens_trans_addrs_t; //data type defining the start addresses of the tensors

typedef struct packed
{
    tens_trans_cfg_t   tens_trans_cfg;
    tens_trans_addrs_t tens_trans_addrs;
    mtx_trans_dims_t   tens_trans_lin_dims;
    tens_trans_dims_t  tens_trans_conv_dims; 
} tens_trans_spec_t; //data type defining a transformation

typedef struct
{
    int rd_addr_wdt;
    int d_in_wdt;
    int d_out_wdt;
    int pipe_in_cnt;
    int pipe_out_cnt;
} mem_cmd_t;

function automatic int round_npow2(int x); 
    return 2**($clog2(x));
endfunction

function automatic bit data_type_mov_or_stat(pipe_data_type_t data_type); 
    return data_type == TYPE_DATA | data_type == TYPE_STAT_WEIGHT;
endfunction

function automatic bit side_ch_match_vect(pipe_data_t data_vect[C_VECT_SIZE-1:0]); 
    bit res = 1;

    for(int i = 0; i < C_VECT_SIZE-1; i++) begin
        if(data_vect[i].data_last       != data_vect[i+1].data_last | 
           data_vect[i].data_type       != data_vect[i+1].data_type | 
           data_vect[i].data_val        != data_vect[i+1].data_val)
           res = 0;
    end

    return res;

endfunction

endpackage