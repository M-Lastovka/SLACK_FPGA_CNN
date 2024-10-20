// Created with Corsair v1.0.4
package regmap_reg_pckg;

parameter CSR_BASE_ADDR = 0;
parameter CSR_DATA_WIDTH = 32;
parameter CSR_ADDR_WIDTH = 32;

// CNN_ACCEL_CTRL_REG
parameter C_CTRL_REG_ADDR = 32'h0;
parameter C_CTRL_REG_RESET = 32'h0;

// CNN_ACCEL_CTRL_REG.TENS_TRANS_SEQ_START
parameter C_CTRL_REG_TENS_TRANS_SEQ_START_WIDTH = 1;
parameter C_CTRL_REG_TENS_TRANS_SEQ_START_LSB = 0;
parameter C_CTRL_REG_TENS_TRANS_SEQ_START_MASK = 32'h1;
parameter C_CTRL_REG_TENS_TRANS_SEQ_START_RESET = 1'h0;

// CNN_ACCEL_CTRL_REG.TENS_TRANS_SEQ_LEN
parameter C_CTRL_REG_TENS_TRANS_SEQ_LEN_WIDTH = 10;
parameter C_CTRL_REG_TENS_TRANS_SEQ_LEN_LSB = 1;
parameter C_CTRL_REG_TENS_TRANS_SEQ_LEN_MASK = 32'h7fe;
parameter C_CTRL_REG_TENS_TRANS_SEQ_LEN_RESET = 10'h0;

// CNN_ACCEL_CTRL_REG.SOFT_RESET
parameter C_CTRL_REG_SOFT_RESET_WIDTH = 1;
parameter C_CTRL_REG_SOFT_RESET_LSB = 11;
parameter C_CTRL_REG_SOFT_RESET_MASK = 32'h800;
parameter C_CTRL_REG_SOFT_RESET_RESET = 1'h0;


// CNN_ACCEL_STAT_REG
parameter C_STAT_REG_ADDR = 32'h4;
parameter C_STAT_REG_RESET = 32'h0;

// CNN_ACCEL_STAT_REG.TENS_TRANS_SEQ_BUSY
parameter C_STAT_REG_TENS_TRANS_SEQ_BUSY_WIDTH = 1;
parameter C_STAT_REG_TENS_TRANS_SEQ_BUSY_LSB = 0;
parameter C_STAT_REG_TENS_TRANS_SEQ_BUSY_MASK = 32'h1;
parameter C_STAT_REG_TENS_TRANS_SEQ_BUSY_RESET = 1'h0;

// CNN_ACCEL_STAT_REG.TENS_TRANS_SEQ_CNT
parameter C_STAT_REG_TENS_TRANS_SEQ_CNT_WIDTH = 10;
parameter C_STAT_REG_TENS_TRANS_SEQ_CNT_LSB = 1;
parameter C_STAT_REG_TENS_TRANS_SEQ_CNT_MASK = 32'h7fe;
parameter C_STAT_REG_TENS_TRANS_SEQ_CNT_RESET = 10'h0;


// CNN_ACCEL_INT_REG
parameter C_INT_REG_ADDR = 32'h8;
parameter C_INT_REG_RESET = 32'h0;

// CNN_ACCEL_INT_REG.INT_TENS_TRANS_SEQ_DONE_EN
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_WIDTH = 1;
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_LSB = 0;
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_MASK = 32'h1;
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_RESET = 1'h0;

// CNN_ACCEL_INT_REG.INT_TENS_TRANS_SEQ_DONE_STAT
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_WIDTH = 1;
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_LSB = 1;
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_MASK = 32'h2;
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_RESET = 1'h0;

// CNN_ACCEL_INT_REG.INT_TENS_TRANS_SEQ_DONE_CLEAR
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_WIDTH = 1;
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_LSB = 2;
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_MASK = 32'h4;
parameter C_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_RESET = 1'h0;

// CNN_ACCEL_INT_REG.INT_STREAM_H2C_DONE_EN
parameter C_INT_REG_INT_STREAM_H2C_DONE_EN_WIDTH = 1;
parameter C_INT_REG_INT_STREAM_H2C_DONE_EN_LSB = 3;
parameter C_INT_REG_INT_STREAM_H2C_DONE_EN_MASK = 32'h8;
parameter C_INT_REG_INT_STREAM_H2C_DONE_EN_RESET = 1'h0;

// CNN_ACCEL_INT_REG.INT_STREAM_H2C_DONE_STAT
parameter C_INT_REG_INT_STREAM_H2C_DONE_STAT_WIDTH = 1;
parameter C_INT_REG_INT_STREAM_H2C_DONE_STAT_LSB = 4;
parameter C_INT_REG_INT_STREAM_H2C_DONE_STAT_MASK = 32'h10;
parameter C_INT_REG_INT_STREAM_H2C_DONE_STAT_RESET = 1'h0;

// CNN_ACCEL_INT_REG.INT_STREAM_H2C_DONE_CLEAR
parameter C_INT_REG_INT_STREAM_H2C_DONE_CLEAR_WIDTH = 1;
parameter C_INT_REG_INT_STREAM_H2C_DONE_CLEAR_LSB = 5;
parameter C_INT_REG_INT_STREAM_H2C_DONE_CLEAR_MASK = 32'h20;
parameter C_INT_REG_INT_STREAM_H2C_DONE_CLEAR_RESET = 1'h0;

// CNN_ACCEL_INT_REG.INT_STREAM_C2H_DONE_EN
parameter C_INT_REG_INT_STREAM_C2H_DONE_EN_WIDTH = 1;
parameter C_INT_REG_INT_STREAM_C2H_DONE_EN_LSB = 6;
parameter C_INT_REG_INT_STREAM_C2H_DONE_EN_MASK = 32'h40;
parameter C_INT_REG_INT_STREAM_C2H_DONE_EN_RESET = 1'h0;

// CNN_ACCEL_INT_REG.INT_STREAM_C2H_DONE_STAT
parameter C_INT_REG_INT_STREAM_C2H_DONE_STAT_WIDTH = 1;
parameter C_INT_REG_INT_STREAM_C2H_DONE_STAT_LSB = 7;
parameter C_INT_REG_INT_STREAM_C2H_DONE_STAT_MASK = 32'h80;
parameter C_INT_REG_INT_STREAM_C2H_DONE_STAT_RESET = 1'h0;

// CNN_ACCEL_INT_REG.INT_STREAM_C2H_DONE_CLEAR
parameter C_INT_REG_INT_STREAM_C2H_DONE_CLEAR_WIDTH = 1;
parameter C_INT_REG_INT_STREAM_C2H_DONE_CLEAR_LSB = 8;
parameter C_INT_REG_INT_STREAM_C2H_DONE_CLEAR_MASK = 32'h100;
parameter C_INT_REG_INT_STREAM_C2H_DONE_CLEAR_RESET = 1'h0;


// CNN_ACCEL_MMEM_OFFSET_REG
parameter C_MMEM_OFFSET_REG_ADDR = 32'hc;
parameter C_MMEM_OFFSET_REG_RESET = 32'h0;

// CNN_ACCEL_MMEM_OFFSET_REG.MMEM_BASE_ADDR
parameter C_MMEM_OFFSET_REG_MMEM_BASE_ADDR_WIDTH = 32;
parameter C_MMEM_OFFSET_REG_MMEM_BASE_ADDR_LSB = 0;
parameter C_MMEM_OFFSET_REG_MMEM_BASE_ADDR_MASK = 32'hffffffff;
parameter C_MMEM_OFFSET_REG_MMEM_BASE_ADDR_RESET = 32'h0;


// CNN_ACCEL_GP_RW_REG
parameter C_GP_RW_REG_ADDR = 32'h10;
parameter C_GP_RW_REG_RESET = 32'h0;

// CNN_ACCEL_GP_RW_REG.GP_RW
parameter C_GP_RW_REG_GP_RW_WIDTH = 32;
parameter C_GP_RW_REG_GP_RW_LSB = 0;
parameter C_GP_RW_REG_GP_RW_MASK = 32'hffffffff;
parameter C_GP_RW_REG_GP_RW_RESET = 32'h0;


// CNN_ACCEL_PERF_RUN_CTRL_REG
parameter C_PERF_RUN_CTRL_REG_ADDR = 32'h14;
parameter C_PERF_RUN_CTRL_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_RUN_CTRL_REG.PERF_RUN_EN
parameter C_PERF_RUN_CTRL_REG_PERF_RUN_EN_WIDTH = 1;
parameter C_PERF_RUN_CTRL_REG_PERF_RUN_EN_LSB = 0;
parameter C_PERF_RUN_CTRL_REG_PERF_RUN_EN_MASK = 32'h1;
parameter C_PERF_RUN_CTRL_REG_PERF_RUN_EN_RESET = 1'h0;

// CNN_ACCEL_PERF_RUN_CTRL_REG.PERF_RUN_CLEAR
parameter C_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_WIDTH = 1;
parameter C_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_LSB = 1;
parameter C_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_MASK = 32'h2;
parameter C_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_RESET = 1'h0;


// CNN_ACCEL_PERF_RUN_LH_REG
parameter C_PERF_RUN_LH_REG_ADDR = 32'h18;
parameter C_PERF_RUN_LH_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_RUN_LH_REG.PERF_RUN_LH
parameter C_PERF_RUN_LH_REG_PERF_RUN_LH_WIDTH = 32;
parameter C_PERF_RUN_LH_REG_PERF_RUN_LH_LSB = 0;
parameter C_PERF_RUN_LH_REG_PERF_RUN_LH_MASK = 32'hffffffff;
parameter C_PERF_RUN_LH_REG_PERF_RUN_LH_RESET = 32'h0;


// CNN_ACCEL_PERF_RUN_UH_REG
parameter C_PERF_RUN_UH_REG_ADDR = 32'h1c;
parameter C_PERF_RUN_UH_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_RUN_UH_REG.PERF_RUN_UH
parameter C_PERF_RUN_UH_REG_PERF_RUN_UH_WIDTH = 32;
parameter C_PERF_RUN_UH_REG_PERF_RUN_UH_LSB = 0;
parameter C_PERF_RUN_UH_REG_PERF_RUN_UH_MASK = 32'hffffffff;
parameter C_PERF_RUN_UH_REG_PERF_RUN_UH_RESET = 32'h0;


// CNN_ACCEL_PERF_COMP_CTRL_REG
parameter C_PERF_COMP_CTRL_REG_ADDR = 32'h20;
parameter C_PERF_COMP_CTRL_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_COMP_CTRL_REG.PERF_COMP_EN
parameter C_PERF_COMP_CTRL_REG_PERF_COMP_EN_WIDTH = 1;
parameter C_PERF_COMP_CTRL_REG_PERF_COMP_EN_LSB = 0;
parameter C_PERF_COMP_CTRL_REG_PERF_COMP_EN_MASK = 32'h1;
parameter C_PERF_COMP_CTRL_REG_PERF_COMP_EN_RESET = 1'h0;

// CNN_ACCEL_PERF_COMP_CTRL_REG.PERF_COMP_CLEAR
parameter C_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_WIDTH = 1;
parameter C_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_LSB = 1;
parameter C_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_MASK = 32'h2;
parameter C_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_RESET = 1'h0;


// CNN_ACCEL_PERF_COMP_LH_REG
parameter C_PERF_COMP_LH_REG_ADDR = 32'h24;
parameter C_PERF_COMP_LH_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_COMP_LH_REG.PERF_COMP_LH
parameter C_PERF_COMP_LH_REG_PERF_COMP_LH_WIDTH = 32;
parameter C_PERF_COMP_LH_REG_PERF_COMP_LH_LSB = 0;
parameter C_PERF_COMP_LH_REG_PERF_COMP_LH_MASK = 32'hffffffff;
parameter C_PERF_COMP_LH_REG_PERF_COMP_LH_RESET = 32'h0;


// CNN_ACCEL_PERF_COMP_UH_REG
parameter C_PERF_COMP_UH_REG_ADDR = 32'h28;
parameter C_PERF_COMP_UH_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_COMP_UH_REG.PERF_COMP_UH
parameter C_PERF_COMP_UH_REG_PERF_COMP_UH_WIDTH = 32;
parameter C_PERF_COMP_UH_REG_PERF_COMP_UH_LSB = 0;
parameter C_PERF_COMP_UH_REG_PERF_COMP_UH_MASK = 32'hffffffff;
parameter C_PERF_COMP_UH_REG_PERF_COMP_UH_RESET = 32'h0;


// CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG
parameter C_PERF_STREAM_C2H_CTRL_REG_ADDR = 32'h2c;
parameter C_PERF_STREAM_C2H_CTRL_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG.PERF_STREAM_EN
parameter C_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_WIDTH = 1;
parameter C_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_LSB = 0;
parameter C_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_MASK = 32'h1;
parameter C_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_RESET = 1'h0;

// CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG.PERF_STREAM_CLEAR
parameter C_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_WIDTH = 1;
parameter C_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_LSB = 1;
parameter C_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_MASK = 32'h2;
parameter C_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_RESET = 1'h0;


// CNN_ACCEL_PERF_STREAM_C2H_LH_REG
parameter C_PERF_STREAM_C2H_LH_REG_ADDR = 32'h30;
parameter C_PERF_STREAM_C2H_LH_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_STREAM_C2H_LH_REG.PERF_STREAM_LH
parameter C_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_WIDTH = 32;
parameter C_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_LSB = 0;
parameter C_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_MASK = 32'hffffffff;
parameter C_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_RESET = 32'h0;


// CNN_ACCEL_PERF_STREAM_C2H_UH_REG
parameter C_PERF_STREAM_C2H_UH_REG_ADDR = 32'h34;
parameter C_PERF_STREAM_C2H_UH_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_STREAM_C2H_UH_REG.PERF_STREAM_UH
parameter C_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_WIDTH = 32;
parameter C_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_LSB = 0;
parameter C_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_MASK = 32'hffffffff;
parameter C_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_RESET = 32'h0;


// CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG
parameter C_PERF_STREAM_H2C_CTRL_REG_ADDR = 32'h38;
parameter C_PERF_STREAM_H2C_CTRL_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG.PERF_STREAM_EN
parameter C_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_WIDTH = 1;
parameter C_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_LSB = 0;
parameter C_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_MASK = 32'h1;
parameter C_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_RESET = 1'h0;

// CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG.PERF_STREAM_CLEAR
parameter C_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_WIDTH = 1;
parameter C_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_LSB = 1;
parameter C_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_MASK = 32'h2;
parameter C_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_RESET = 1'h0;


// CNN_ACCEL_PERF_STREAM_H2C_LH_REG
parameter C_PERF_STREAM_H2C_LH_REG_ADDR = 32'h3c;
parameter C_PERF_STREAM_H2C_LH_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_STREAM_H2C_LH_REG.PERF_STREAM_LH
parameter C_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_WIDTH = 32;
parameter C_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_LSB = 0;
parameter C_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_MASK = 32'hffffffff;
parameter C_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_RESET = 32'h0;


// CNN_ACCEL_PERF_STREAM_H2C_UH_REG
parameter C_PERF_STREAM_H2C_UH_REG_ADDR = 32'h40;
parameter C_PERF_STREAM_H2C_UH_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_STREAM_H2C_UH_REG.PERF_STREAM_UH
parameter C_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_WIDTH = 32;
parameter C_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_LSB = 0;
parameter C_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_MASK = 32'hffffffff;
parameter C_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_RESET = 32'h0;


// CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG
parameter C_PERF_CACHE_STALL_CTRL_REG_ADDR = 32'h44;
parameter C_PERF_CACHE_STALL_CTRL_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG.PERF_STREAM_EN
parameter C_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_WIDTH = 1;
parameter C_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_LSB = 0;
parameter C_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_MASK = 32'h1;
parameter C_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_RESET = 1'h0;

// CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG.PERF_STREAM_CLEAR
parameter C_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_WIDTH = 1;
parameter C_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_LSB = 1;
parameter C_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_MASK = 32'h2;
parameter C_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_RESET = 1'h0;


// CNN_ACCEL_PERF_CACHE_STALL_LH_REG
parameter C_PERF_CACHE_STALL_LH_REG_ADDR = 32'h48;
parameter C_PERF_CACHE_STALL_LH_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_CACHE_STALL_LH_REG.PERF_STREAM_LH
parameter C_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_WIDTH = 32;
parameter C_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_LSB = 0;
parameter C_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_MASK = 32'hffffffff;
parameter C_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_RESET = 32'h0;


// CNN_ACCEL_PERF_CACHE_STALL_UH_REG
parameter C_PERF_CACHE_STALL_UH_REG_ADDR = 32'h4c;
parameter C_PERF_CACHE_STALL_UH_REG_RESET = 32'h0;

// CNN_ACCEL_PERF_CACHE_STALL_UH_REG.PERF_STREAM_UH
parameter C_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_WIDTH = 32;
parameter C_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_LSB = 0;
parameter C_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_MASK = 32'hffffffff;
parameter C_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_RESET = 32'h0;


// CNN_ACCEL_TENS_TRANS_CFG_REG
parameter C_TENS_TRANS_CFG_REG_ADDR = 32'h50;
parameter C_TENS_TRANS_CFG_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_CFG_REG.TENS_TRANS_TYPE
parameter C_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_WIDTH = 4;
parameter C_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_LSB = 0;
parameter C_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_MASK = 32'hf;
parameter C_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_RESET = 4'h0;

// CNN_ACCEL_TENS_TRANS_CFG_REG.NLIN_F_TYPE
parameter C_TENS_TRANS_CFG_REG_NLIN_F_TYPE_WIDTH = 4;
parameter C_TENS_TRANS_CFG_REG_NLIN_F_TYPE_LSB = 4;
parameter C_TENS_TRANS_CFG_REG_NLIN_F_TYPE_MASK = 32'hf0;
parameter C_TENS_TRANS_CFG_REG_NLIN_F_TYPE_RESET = 4'h0;

// CNN_ACCEL_TENS_TRANS_CFG_REG.BATCH_NORM_EN
parameter C_TENS_TRANS_CFG_REG_BATCH_NORM_EN_WIDTH = 1;
parameter C_TENS_TRANS_CFG_REG_BATCH_NORM_EN_LSB = 8;
parameter C_TENS_TRANS_CFG_REG_BATCH_NORM_EN_MASK = 32'h100;
parameter C_TENS_TRANS_CFG_REG_BATCH_NORM_EN_RESET = 1'h0;

// CNN_ACCEL_TENS_TRANS_CFG_REG.REPL_BIAS
parameter C_TENS_TRANS_CFG_REG_REPL_BIAS_WIDTH = 1;
parameter C_TENS_TRANS_CFG_REG_REPL_BIAS_LSB = 9;
parameter C_TENS_TRANS_CFG_REG_REPL_BIAS_MASK = 32'h200;
parameter C_TENS_TRANS_CFG_REG_REPL_BIAS_RESET = 1'h0;

// CNN_ACCEL_TENS_TRANS_CFG_REG.BIAS_EN
parameter C_TENS_TRANS_CFG_REG_BIAS_EN_WIDTH = 1;
parameter C_TENS_TRANS_CFG_REG_BIAS_EN_LSB = 10;
parameter C_TENS_TRANS_CFG_REG_BIAS_EN_MASK = 32'h400;
parameter C_TENS_TRANS_CFG_REG_BIAS_EN_RESET = 1'h0;


// CNN_ACCEL_TENS_TRANS_CONV_CFG_REG
parameter C_TENS_TRANS_CONV_CFG_REG_ADDR = 32'h54;
parameter C_TENS_TRANS_CONV_CFG_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_CONV_CFG_REG.CONV_STRIDE_0
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_WIDTH = 8;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_LSB = 0;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_MASK = 32'hff;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_RESET = 8'h0;

// CNN_ACCEL_TENS_TRANS_CONV_CFG_REG.CONV_STRIDE_1
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_WIDTH = 8;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_LSB = 8;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_MASK = 32'hff00;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_RESET = 8'h0;

// CNN_ACCEL_TENS_TRANS_CONV_CFG_REG.CONV_PADDING_0
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_WIDTH = 8;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_LSB = 16;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_MASK = 32'hff0000;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_RESET = 8'h0;

// CNN_ACCEL_TENS_TRANS_CONV_CFG_REG.CONV_PADDING_1
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_WIDTH = 8;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_LSB = 24;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_MASK = 32'hff000000;
parameter C_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_RESET = 8'h0;


// CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG
parameter C_TENS_TRANS_ADDR_SRC_A_REG_ADDR = 32'h58;
parameter C_TENS_TRANS_ADDR_SRC_A_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG.TENS_ADDR
parameter C_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_WIDTH = 32;
parameter C_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_LSB = 0;
parameter C_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_MASK = 32'hffffffff;
parameter C_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_RESET = 32'h0;


// CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG
parameter C_TENS_TRANS_ADDR_SRC_B_REG_ADDR = 32'h5c;
parameter C_TENS_TRANS_ADDR_SRC_B_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG.TENS_ADDR
parameter C_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_WIDTH = 32;
parameter C_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_LSB = 0;
parameter C_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_MASK = 32'hffffffff;
parameter C_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_RESET = 32'h0;


// CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG
parameter C_TENS_TRANS_ADDR_BATCH_NORM_REG_ADDR = 32'h60;
parameter C_TENS_TRANS_ADDR_BATCH_NORM_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG.TENS_ADDR
parameter C_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_WIDTH = 32;
parameter C_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_LSB = 0;
parameter C_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_MASK = 32'hffffffff;
parameter C_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_RESET = 32'h0;


// CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG
parameter C_TENS_TRANS_ADDR_BIAS_REG_ADDR = 32'h64;
parameter C_TENS_TRANS_ADDR_BIAS_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG.TENS_ADDR
parameter C_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_WIDTH = 32;
parameter C_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_LSB = 0;
parameter C_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_MASK = 32'hffffffff;
parameter C_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_RESET = 32'h0;


// CNN_ACCEL_TENS_TRANS_ADDR_RES_REG
parameter C_TENS_TRANS_ADDR_RES_REG_ADDR = 32'h68;
parameter C_TENS_TRANS_ADDR_RES_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_ADDR_RES_REG.TENS_ADDR
parameter C_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_WIDTH = 32;
parameter C_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_LSB = 0;
parameter C_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_MASK = 32'hffffffff;
parameter C_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_RESET = 32'h0;


// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG
parameter C_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR = 32'h6c;
parameter C_TENS_TRANS_LIN_DIMS_SRC_A_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG.TENS_0_DIM
parameter C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_WIDTH = 16;
parameter C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_LSB = 0;
parameter C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_MASK = 32'hffff;
parameter C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_RESET = 16'h0;

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG.TENS_1_DIM
parameter C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_WIDTH = 16;
parameter C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_LSB = 16;
parameter C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_MASK = 32'hffff0000;
parameter C_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_RESET = 16'h0;


// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG
parameter C_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR = 32'h70;
parameter C_TENS_TRANS_LIN_DIMS_SRC_B_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG.TENS_0_DIM
parameter C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_WIDTH = 16;
parameter C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_LSB = 0;
parameter C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_MASK = 32'hffff;
parameter C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_RESET = 16'h0;

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG.TENS_1_DIM
parameter C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_WIDTH = 16;
parameter C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_LSB = 16;
parameter C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_MASK = 32'hffff0000;
parameter C_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_RESET = 16'h0;


// CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG
parameter C_TENS_TRANS_LIN_DIMS_RES_REG_ADDR = 32'h74;
parameter C_TENS_TRANS_LIN_DIMS_RES_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG.TENS_0_DIM
parameter C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_WIDTH = 16;
parameter C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_LSB = 0;
parameter C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_MASK = 32'hffff;
parameter C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_RESET = 16'h0;

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG.TENS_1_DIM
parameter C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_WIDTH = 16;
parameter C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_LSB = 16;
parameter C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_MASK = 32'hffff0000;
parameter C_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_RESET = 16'h0;


// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR = 32'h78;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG.TENS_0_DIM
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_LSB = 0;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_MASK = 32'hffff;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_RESET = 16'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG.TENS_1_DIM
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_LSB = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_MASK = 32'hffff0000;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_RESET = 16'h0;


// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR = 32'h7c;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG.TENS_2_DIM
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_LSB = 0;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_MASK = 32'hffff;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_RESET = 16'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG.TENS_3_DIM
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_LSB = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_MASK = 32'hffff0000;
parameter C_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_RESET = 16'h0;


// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR = 32'h80;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG.TENS_0_DIM
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_LSB = 0;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_MASK = 32'hffff;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_RESET = 16'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG.TENS_1_DIM
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_LSB = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_MASK = 32'hffff0000;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_RESET = 16'h0;


// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR = 32'h84;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG.TENS_2_DIM
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_LSB = 0;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_MASK = 32'hffff;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_RESET = 16'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG.TENS_3_DIM
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_LSB = 16;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_MASK = 32'hffff0000;
parameter C_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_RESET = 16'h0;


// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG
parameter C_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR = 32'h88;
parameter C_TENS_TRANS_CONV_DIMS_RES_0_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG.TENS_0_DIM
parameter C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_LSB = 0;
parameter C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_MASK = 32'hffff;
parameter C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_RESET = 16'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG.TENS_1_DIM
parameter C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_LSB = 16;
parameter C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_MASK = 32'hffff0000;
parameter C_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_RESET = 16'h0;


// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG
parameter C_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR = 32'h8c;
parameter C_TENS_TRANS_CONV_DIMS_RES_1_REG_RESET = 32'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG.TENS_2_DIM
parameter C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_LSB = 0;
parameter C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_MASK = 32'hffff;
parameter C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_RESET = 16'h0;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG.TENS_3_DIM
parameter C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_WIDTH = 16;
parameter C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_LSB = 16;
parameter C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_MASK = 32'hffff0000;
parameter C_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_RESET = 16'h0;


endpackage