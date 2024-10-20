// Created with Corsair v1.0.4
#ifndef __CNN_ACCEL_REGMAP_H
#define __CNN_ACCEL_REGMAP_H

#define __I  volatile const // 'read only' permissions
#define __O  volatile       // 'write only' permissions
#define __IO volatile       // 'read / write' permissions


#ifdef __cplusplus
#include <cstdint>
extern "C" {
#else
#include <stdint.h>
#endif

#define CSR_BASE_ADDR 0x0

// CNN_ACCEL_CTRL_REG - main control register
#define CSR_CNN_ACCEL_CTRL_REG_ADDR 0x0
#define CSR_CNN_ACCEL_CTRL_REG_RESET 0x0
typedef struct {
    uint32_t TENS_TRANS_SEQ_START : 1; // start signal to execute the tensor trans. sequence
    uint32_t TENS_TRANS_SEQ_LEN : 10; // number of operations in the tensor trans. sequence to be executed
    uint32_t SOFT_RESET : 1; // global software reset, active high
    uint32_t : 20; // reserved
} csr_cnn_accel_ctrl_reg_t;

// CNN_ACCEL_CTRL_REG.TENS_TRANS_SEQ_START - start signal to execute the tensor trans. sequence
#define CSR_CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_START_WIDTH 1
#define CSR_CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_START_LSB 0
#define CSR_CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_START_MASK 0x1
#define CSR_CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_START_RESET 0x0

// CNN_ACCEL_CTRL_REG.TENS_TRANS_SEQ_LEN - number of operations in the tensor trans. sequence to be executed
#define CSR_CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_WIDTH 10
#define CSR_CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_LSB 1
#define CSR_CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_MASK 0x7fe
#define CSR_CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_RESET 0x0

// CNN_ACCEL_CTRL_REG.SOFT_RESET - global software reset, active high
#define CSR_CNN_ACCEL_CTRL_REG_SOFT_RESET_WIDTH 1
#define CSR_CNN_ACCEL_CTRL_REG_SOFT_RESET_LSB 11
#define CSR_CNN_ACCEL_CTRL_REG_SOFT_RESET_MASK 0x800
#define CSR_CNN_ACCEL_CTRL_REG_SOFT_RESET_RESET 0x0

// CNN_ACCEL_STAT_REG - main status register
#define CSR_CNN_ACCEL_STAT_REG_ADDR 0x4
#define CSR_CNN_ACCEL_STAT_REG_RESET 0x0
typedef struct {
    uint32_t TENS_TRANS_SEQ_BUSY : 1; // active high if tensor trans. sequence is progressing
    uint32_t TENS_TRANS_SEQ_CNT : 10; // index of the current trans. sequence in progress
    uint32_t : 21; // reserved
} csr_cnn_accel_stat_reg_t;

// CNN_ACCEL_STAT_REG.TENS_TRANS_SEQ_BUSY - active high if tensor trans. sequence is progressing
#define CSR_CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_BUSY_WIDTH 1
#define CSR_CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_BUSY_LSB 0
#define CSR_CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_BUSY_MASK 0x1
#define CSR_CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_BUSY_RESET 0x0

// CNN_ACCEL_STAT_REG.TENS_TRANS_SEQ_CNT - index of the current trans. sequence in progress
#define CSR_CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_CNT_WIDTH 10
#define CSR_CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_CNT_LSB 1
#define CSR_CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_CNT_MASK 0x7fe
#define CSR_CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_CNT_RESET 0x0

// CNN_ACCEL_INT_REG - main interrupt register, reserved for future use, currently only registers implemented
#define CSR_CNN_ACCEL_INT_REG_ADDR 0x8
#define CSR_CNN_ACCEL_INT_REG_RESET 0x0
typedef struct {
    uint32_t INT_TENS_TRANS_SEQ_DONE_EN : 1; // interrupt enable - tensor transformation sequence done
    uint32_t INT_TENS_TRANS_SEQ_DONE_STAT : 1; // interrupt status - tensor transformation sequence done
    uint32_t INT_TENS_TRANS_SEQ_DONE_CLEAR : 1; // interrupt clear - tensor transformation sequence done
    uint32_t INT_STREAM_H2C_DONE_EN : 1; // interrupt enable - tensor transformation sequence done
    uint32_t INT_STREAM_H2C_DONE_STAT : 1; // interrupt status - tensor transformation sequence done
    uint32_t INT_STREAM_H2C_DONE_CLEAR : 1; // interrupt clear - tensor transformation sequence done
    uint32_t INT_STREAM_C2H_DONE_EN : 1; // interrupt enable - tensor transformation sequence done
    uint32_t INT_STREAM_C2H_DONE_STAT : 1; // interrupt status - tensor transformation sequence done
    uint32_t INT_STREAM_C2H_DONE_CLEAR : 1; // interrupt clear - tensor transformation sequence done
    uint32_t : 23; // reserved
} csr_cnn_accel_int_reg_t;

// CNN_ACCEL_INT_REG.INT_TENS_TRANS_SEQ_DONE_EN - interrupt enable - tensor transformation sequence done
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_WIDTH 1
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_LSB 0
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_MASK 0x1
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_RESET 0x0

// CNN_ACCEL_INT_REG.INT_TENS_TRANS_SEQ_DONE_STAT - interrupt status - tensor transformation sequence done
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_WIDTH 1
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_LSB 1
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_MASK 0x2
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_RESET 0x0

// CNN_ACCEL_INT_REG.INT_TENS_TRANS_SEQ_DONE_CLEAR - interrupt clear - tensor transformation sequence done
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_WIDTH 1
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_LSB 2
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_MASK 0x4
#define CSR_CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_RESET 0x0

// CNN_ACCEL_INT_REG.INT_STREAM_H2C_DONE_EN - interrupt enable - tensor transformation sequence done
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_WIDTH 1
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_LSB 3
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_MASK 0x8
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_RESET 0x0

// CNN_ACCEL_INT_REG.INT_STREAM_H2C_DONE_STAT - interrupt status - tensor transformation sequence done
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_STAT_WIDTH 1
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_STAT_LSB 4
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_STAT_MASK 0x10
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_STAT_RESET 0x0

// CNN_ACCEL_INT_REG.INT_STREAM_H2C_DONE_CLEAR - interrupt clear - tensor transformation sequence done
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_CLEAR_WIDTH 1
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_CLEAR_LSB 5
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_CLEAR_MASK 0x20
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_CLEAR_RESET 0x0

// CNN_ACCEL_INT_REG.INT_STREAM_C2H_DONE_EN - interrupt enable - tensor transformation sequence done
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_WIDTH 1
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_LSB 6
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_MASK 0x40
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_RESET 0x0

// CNN_ACCEL_INT_REG.INT_STREAM_C2H_DONE_STAT - interrupt status - tensor transformation sequence done
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_STAT_WIDTH 1
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_STAT_LSB 7
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_STAT_MASK 0x80
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_STAT_RESET 0x0

// CNN_ACCEL_INT_REG.INT_STREAM_C2H_DONE_CLEAR - interrupt clear - tensor transformation sequence done
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_CLEAR_WIDTH 1
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_CLEAR_LSB 8
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_CLEAR_MASK 0x100
#define CSR_CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_CLEAR_RESET 0x0

// CNN_ACCEL_MMEM_OFFSET_REG - address offset for the main memory access, reserved for future use, currently only registers implemented
#define CSR_CNN_ACCEL_MMEM_OFFSET_REG_ADDR 0xc
#define CSR_CNN_ACCEL_MMEM_OFFSET_REG_RESET 0x0
typedef struct {
    uint32_t MMEM_BASE_ADDR : 32; // base address value
} csr_cnn_accel_mmem_offset_reg_t;

// CNN_ACCEL_MMEM_OFFSET_REG.MMEM_BASE_ADDR - base address value
#define CSR_CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_WIDTH 32
#define CSR_CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_LSB 0
#define CSR_CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_MASK 0xffffffff
#define CSR_CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_RESET 0x0

// CNN_ACCEL_GP_RW_REG - general purpose read-write register, reserved for future use
#define CSR_CNN_ACCEL_GP_RW_REG_ADDR 0x10
#define CSR_CNN_ACCEL_GP_RW_REG_RESET 0x0
typedef struct {
    uint32_t GP_RW : 32; // general purpose register
} csr_cnn_accel_gp_rw_reg_t;

// CNN_ACCEL_GP_RW_REG.GP_RW - general purpose register
#define CSR_CNN_ACCEL_GP_RW_REG_GP_RW_WIDTH 32
#define CSR_CNN_ACCEL_GP_RW_REG_GP_RW_LSB 0
#define CSR_CNN_ACCEL_GP_RW_REG_GP_RW_MASK 0xffffffff
#define CSR_CNN_ACCEL_GP_RW_REG_GP_RW_RESET 0x0

// CNN_ACCEL_PERF_RUN_CTRL_REG - performance counter - total run cycles - control register
#define CSR_CNN_ACCEL_PERF_RUN_CTRL_REG_ADDR 0x14
#define CSR_CNN_ACCEL_PERF_RUN_CTRL_REG_RESET 0x0
typedef struct {
    uint32_t PERF_RUN_EN : 1; // perf. counter enable
    uint32_t PERF_RUN_CLEAR : 1; // perf. counter clear
    uint32_t : 30; // reserved
} csr_cnn_accel_perf_run_ctrl_reg_t;

// CNN_ACCEL_PERF_RUN_CTRL_REG.PERF_RUN_EN - perf. counter enable
#define CSR_CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_WIDTH 1
#define CSR_CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_LSB 0
#define CSR_CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_MASK 0x1
#define CSR_CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_RESET 0x0

// CNN_ACCEL_PERF_RUN_CTRL_REG.PERF_RUN_CLEAR - perf. counter clear
#define CSR_CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_WIDTH 1
#define CSR_CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_LSB 1
#define CSR_CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_MASK 0x2
#define CSR_CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_RESET 0x0

// CNN_ACCEL_PERF_RUN_LH_REG - performance counter - run cycles - lower half
#define CSR_CNN_ACCEL_PERF_RUN_LH_REG_ADDR 0x18
#define CSR_CNN_ACCEL_PERF_RUN_LH_REG_RESET 0x0
typedef struct {
    uint32_t PERF_RUN_LH : 32; // perf. counter value
} csr_cnn_accel_perf_run_lh_reg_t;

// CNN_ACCEL_PERF_RUN_LH_REG.PERF_RUN_LH - perf. counter value
#define CSR_CNN_ACCEL_PERF_RUN_LH_REG_PERF_RUN_LH_WIDTH 32
#define CSR_CNN_ACCEL_PERF_RUN_LH_REG_PERF_RUN_LH_LSB 0
#define CSR_CNN_ACCEL_PERF_RUN_LH_REG_PERF_RUN_LH_MASK 0xffffffff
#define CSR_CNN_ACCEL_PERF_RUN_LH_REG_PERF_RUN_LH_RESET 0x0

// CNN_ACCEL_PERF_RUN_UH_REG - performance counter - run cycles - upper half
#define CSR_CNN_ACCEL_PERF_RUN_UH_REG_ADDR 0x1c
#define CSR_CNN_ACCEL_PERF_RUN_UH_REG_RESET 0x0
typedef struct {
    uint32_t PERF_RUN_UH : 32; // perf. counter value
} csr_cnn_accel_perf_run_uh_reg_t;

// CNN_ACCEL_PERF_RUN_UH_REG.PERF_RUN_UH - perf. counter value
#define CSR_CNN_ACCEL_PERF_RUN_UH_REG_PERF_RUN_UH_WIDTH 32
#define CSR_CNN_ACCEL_PERF_RUN_UH_REG_PERF_RUN_UH_LSB 0
#define CSR_CNN_ACCEL_PERF_RUN_UH_REG_PERF_RUN_UH_MASK 0xffffffff
#define CSR_CNN_ACCEL_PERF_RUN_UH_REG_PERF_RUN_UH_RESET 0x0

// CNN_ACCEL_PERF_COMP_CTRL_REG - performance counter - computation cycles - control register
#define CSR_CNN_ACCEL_PERF_COMP_CTRL_REG_ADDR 0x20
#define CSR_CNN_ACCEL_PERF_COMP_CTRL_REG_RESET 0x0
typedef struct {
    uint32_t PERF_COMP_EN : 1; // perf. counter enable
    uint32_t PERF_COMP_CLEAR : 1; // perf. counter clear
    uint32_t : 30; // reserved
} csr_cnn_accel_perf_comp_ctrl_reg_t;

// CNN_ACCEL_PERF_COMP_CTRL_REG.PERF_COMP_EN - perf. counter enable
#define CSR_CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_WIDTH 1
#define CSR_CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_LSB 0
#define CSR_CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_MASK 0x1
#define CSR_CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_RESET 0x0

// CNN_ACCEL_PERF_COMP_CTRL_REG.PERF_COMP_CLEAR - perf. counter clear
#define CSR_CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_WIDTH 1
#define CSR_CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_LSB 1
#define CSR_CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_MASK 0x2
#define CSR_CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_RESET 0x0

// CNN_ACCEL_PERF_COMP_LH_REG - performance counter - run cycles - lower half
#define CSR_CNN_ACCEL_PERF_COMP_LH_REG_ADDR 0x24
#define CSR_CNN_ACCEL_PERF_COMP_LH_REG_RESET 0x0
typedef struct {
    uint32_t PERF_COMP_LH : 32; // perf. counter value
} csr_cnn_accel_perf_comp_lh_reg_t;

// CNN_ACCEL_PERF_COMP_LH_REG.PERF_COMP_LH - perf. counter value
#define CSR_CNN_ACCEL_PERF_COMP_LH_REG_PERF_COMP_LH_WIDTH 32
#define CSR_CNN_ACCEL_PERF_COMP_LH_REG_PERF_COMP_LH_LSB 0
#define CSR_CNN_ACCEL_PERF_COMP_LH_REG_PERF_COMP_LH_MASK 0xffffffff
#define CSR_CNN_ACCEL_PERF_COMP_LH_REG_PERF_COMP_LH_RESET 0x0

// CNN_ACCEL_PERF_COMP_UH_REG - performance counter - run cycles - upper half
#define CSR_CNN_ACCEL_PERF_COMP_UH_REG_ADDR 0x28
#define CSR_CNN_ACCEL_PERF_COMP_UH_REG_RESET 0x0
typedef struct {
    uint32_t PERF_COMP_UH : 32; // perf. counter value
} csr_cnn_accel_perf_comp_uh_reg_t;

// CNN_ACCEL_PERF_COMP_UH_REG.PERF_COMP_UH - perf. counter value
#define CSR_CNN_ACCEL_PERF_COMP_UH_REG_PERF_COMP_UH_WIDTH 32
#define CSR_CNN_ACCEL_PERF_COMP_UH_REG_PERF_COMP_UH_LSB 0
#define CSR_CNN_ACCEL_PERF_COMP_UH_REG_PERF_COMP_UH_MASK 0xffffffff
#define CSR_CNN_ACCEL_PERF_COMP_UH_REG_PERF_COMP_UH_RESET 0x0

// CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG - performance counter - stream C2H cycles - control register
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_ADDR 0x2c
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_RESET 0x0
typedef struct {
    uint32_t PERF_STREAM_EN : 1; // perf. counter enable
    uint32_t PERF_STREAM_CLEAR : 1; // perf. counter clear
    uint32_t : 30; // reserved
} csr_cnn_accel_perf_stream_c2h_ctrl_reg_t;

// CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG.PERF_STREAM_EN - perf. counter enable
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_WIDTH 1
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_LSB 0
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_MASK 0x1
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_RESET 0x0

// CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG.PERF_STREAM_CLEAR - perf. counter clear
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_WIDTH 1
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_LSB 1
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_MASK 0x2
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_RESET 0x0

// CNN_ACCEL_PERF_STREAM_C2H_LH_REG - performance counter - run cycles - lower half
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_LH_REG_ADDR 0x30
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_LH_REG_RESET 0x0
typedef struct {
    uint32_t PERF_STREAM_LH : 32; // perf. counter value
} csr_cnn_accel_perf_stream_c2h_lh_reg_t;

// CNN_ACCEL_PERF_STREAM_C2H_LH_REG.PERF_STREAM_LH - perf. counter value
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_WIDTH 32
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_LSB 0
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_MASK 0xffffffff
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_RESET 0x0

// CNN_ACCEL_PERF_STREAM_C2H_UH_REG - performance counter - run cycles - upper half
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_UH_REG_ADDR 0x34
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_UH_REG_RESET 0x0
typedef struct {
    uint32_t PERF_STREAM_UH : 32; // perf. counter value
} csr_cnn_accel_perf_stream_c2h_uh_reg_t;

// CNN_ACCEL_PERF_STREAM_C2H_UH_REG.PERF_STREAM_UH - perf. counter value
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_WIDTH 32
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_LSB 0
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_MASK 0xffffffff
#define CSR_CNN_ACCEL_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_RESET 0x0

// CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG - performance counter - stream H2C cycles - control register
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_ADDR 0x38
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_RESET 0x0
typedef struct {
    uint32_t PERF_STREAM_EN : 1; // perf. counter enable
    uint32_t PERF_STREAM_CLEAR : 1; // perf. counter clear
    uint32_t : 30; // reserved
} csr_cnn_accel_perf_stream_h2c_ctrl_reg_t;

// CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG.PERF_STREAM_EN - perf. counter enable
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_WIDTH 1
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_LSB 0
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_MASK 0x1
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_RESET 0x0

// CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG.PERF_STREAM_CLEAR - perf. counter clear
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_WIDTH 1
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_LSB 1
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_MASK 0x2
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_RESET 0x0

// CNN_ACCEL_PERF_STREAM_H2C_LH_REG - performance counter - run cycles - lower half
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_LH_REG_ADDR 0x3c
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_LH_REG_RESET 0x0
typedef struct {
    uint32_t PERF_STREAM_LH : 32; // perf. counter value
} csr_cnn_accel_perf_stream_h2c_lh_reg_t;

// CNN_ACCEL_PERF_STREAM_H2C_LH_REG.PERF_STREAM_LH - perf. counter value
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_WIDTH 32
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_LSB 0
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_MASK 0xffffffff
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_RESET 0x0

// CNN_ACCEL_PERF_STREAM_H2C_UH_REG - performance counter - run cycles - upper half
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_UH_REG_ADDR 0x40
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_UH_REG_RESET 0x0
typedef struct {
    uint32_t PERF_STREAM_UH : 32; // perf. counter value
} csr_cnn_accel_perf_stream_h2c_uh_reg_t;

// CNN_ACCEL_PERF_STREAM_H2C_UH_REG.PERF_STREAM_UH - perf. counter value
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_WIDTH 32
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_LSB 0
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_MASK 0xffffffff
#define CSR_CNN_ACCEL_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_RESET 0x0

// CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG - performance counter - cache stall - control register, reserved for future use, currently only registers implemented
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_ADDR 0x44
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_RESET 0x0
typedef struct {
    uint32_t PERF_STREAM_EN : 1; // perf. counter enable
    uint32_t PERF_STREAM_CLEAR : 1; // perf. counter clear
    uint32_t : 30; // reserved
} csr_cnn_accel_perf_cache_stall_ctrl_reg_t;

// CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG.PERF_STREAM_EN - perf. counter enable
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_WIDTH 1
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_LSB 0
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_MASK 0x1
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_RESET 0x0

// CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG.PERF_STREAM_CLEAR - perf. counter clear
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_WIDTH 1
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_LSB 1
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_MASK 0x2
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_RESET 0x0

// CNN_ACCEL_PERF_CACHE_STALL_LH_REG - performance counter - run cycles - lower half, reserved for future use, currently only registers implemented
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_LH_REG_ADDR 0x48
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_LH_REG_RESET 0x0
typedef struct {
    uint32_t PERF_STREAM_LH : 32; // perf. counter value
} csr_cnn_accel_perf_cache_stall_lh_reg_t;

// CNN_ACCEL_PERF_CACHE_STALL_LH_REG.PERF_STREAM_LH - perf. counter value
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_WIDTH 32
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_LSB 0
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_MASK 0xffffffff
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_RESET 0x0

// CNN_ACCEL_PERF_CACHE_STALL_UH_REG - performance counter - run cycles - upper half, reserved for future use, currently only registers implemented
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_UH_REG_ADDR 0x4c
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_UH_REG_RESET 0x0
typedef struct {
    uint32_t PERF_STREAM_UH : 32; // perf. counter value
} csr_cnn_accel_perf_cache_stall_uh_reg_t;

// CNN_ACCEL_PERF_CACHE_STALL_UH_REG.PERF_STREAM_UH - perf. counter value
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_WIDTH 32
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_LSB 0
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_MASK 0xffffffff
#define CSR_CNN_ACCEL_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CFG_REG - tensor trans. configuration
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR 0x50
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_RESET 0x0
typedef struct {
    uint32_t TENS_TRANS_TYPE : 4; // tensor trans. type
    uint32_t NLIN_F_TYPE : 4; // nonlin. function type
    uint32_t BATCH_NORM_EN : 1; // batch normalization enable
    uint32_t REPL_BIAS : 1; // replicate bias flag
    uint32_t BIAS_EN : 1; // bias enable
    uint32_t : 21; // reserved
} csr_cnn_accel_tens_trans_cfg_reg_t;

// CNN_ACCEL_TENS_TRANS_CFG_REG.TENS_TRANS_TYPE - tensor trans. type
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_WIDTH 4
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_MASK 0xf
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CFG_REG.NLIN_F_TYPE - nonlin. function type
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_WIDTH 4
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_LSB 4
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_MASK 0xf0
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CFG_REG.BATCH_NORM_EN - batch normalization enable
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_WIDTH 1
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_LSB 8
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_MASK 0x100
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CFG_REG.REPL_BIAS - replicate bias flag
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_WIDTH 1
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_LSB 9
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_MASK 0x200
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CFG_REG.BIAS_EN - bias enable
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_WIDTH 1
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_LSB 10
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_MASK 0x400
#define CSR_CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_CFG_REG - convolution configuration
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR 0x54
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_RESET 0x0
typedef struct {
    uint32_t CONV_STRIDE_0 : 8; // convolution stride
    uint32_t CONV_STRIDE_1 : 8; // convolution stride
    uint32_t CONV_PADDING_0 : 8; // convolution zero padding
    uint32_t CONV_PADDING_1 : 8; // convolution zero padding
} csr_cnn_accel_tens_trans_conv_cfg_reg_t;

// CNN_ACCEL_TENS_TRANS_CONV_CFG_REG.CONV_STRIDE_0 - convolution stride
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_WIDTH 8
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_MASK 0xff
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_CFG_REG.CONV_STRIDE_1 - convolution stride
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_WIDTH 8
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_LSB 8
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_MASK 0xff00
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_CFG_REG.CONV_PADDING_0 - convolution zero padding
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_WIDTH 8
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_LSB 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_MASK 0xff0000
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_CFG_REG.CONV_PADDING_1 - convolution zero padding
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_WIDTH 8
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_LSB 24
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_MASK 0xff000000
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_RESET 0x0

// CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG - tensor start address
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_ADDR 0x58
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_RESET 0x0
typedef struct {
    uint32_t TENS_ADDR : 32; // tensor address
} csr_cnn_accel_tens_trans_addr_src_a_reg_t;

// CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG.TENS_ADDR - tensor address
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_WIDTH 32
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_MASK 0xffffffff
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_RESET 0x0

// CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG - tensor start address
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_ADDR 0x5c
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_RESET 0x0
typedef struct {
    uint32_t TENS_ADDR : 32; // tensor address
} csr_cnn_accel_tens_trans_addr_src_b_reg_t;

// CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG.TENS_ADDR - tensor address
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_WIDTH 32
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_MASK 0xffffffff
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_RESET 0x0

// CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG - tensor start address
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_ADDR 0x60
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_RESET 0x0
typedef struct {
    uint32_t TENS_ADDR : 32; // tensor address
} csr_cnn_accel_tens_trans_addr_batch_norm_reg_t;

// CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG.TENS_ADDR - tensor address
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_WIDTH 32
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_MASK 0xffffffff
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_RESET 0x0

// CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG - tensor start address
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_ADDR 0x64
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_RESET 0x0
typedef struct {
    uint32_t TENS_ADDR : 32; // tensor address
} csr_cnn_accel_tens_trans_addr_bias_reg_t;

// CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG.TENS_ADDR - tensor address
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_WIDTH 32
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_MASK 0xffffffff
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_RESET 0x0

// CNN_ACCEL_TENS_TRANS_ADDR_RES_REG - tensor start address
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_ADDR 0x68
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_RESET 0x0
typedef struct {
    uint32_t TENS_ADDR : 32; // tensor address
} csr_cnn_accel_tens_trans_addr_res_reg_t;

// CNN_ACCEL_TENS_TRANS_ADDR_RES_REG.TENS_ADDR - tensor address
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_WIDTH 32
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_MASK 0xffffffff
#define CSR_CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_RESET 0x0

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG - tensor trans. linear (matrix) dimensions
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR 0x6c
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_RESET 0x0
typedef struct {
    uint32_t TENS_0_DIM : 16; // row size
    uint32_t TENS_1_DIM : 16; // column size
} csr_cnn_accel_tens_trans_lin_dims_src_a_reg_t;

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG.TENS_0_DIM - row size
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_MASK 0xffff
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG.TENS_1_DIM - column size
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_LSB 16
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_MASK 0xffff0000
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG - tensor trans. linear (matrix) dimensions
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR 0x70
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_RESET 0x0
typedef struct {
    uint32_t TENS_0_DIM : 16; // row size
    uint32_t TENS_1_DIM : 16; // column size
} csr_cnn_accel_tens_trans_lin_dims_src_b_reg_t;

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG.TENS_0_DIM - row size
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_MASK 0xffff
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG.TENS_1_DIM - column size
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_LSB 16
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_MASK 0xffff0000
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG - tensor trans. linear (matrix) dimensions
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR 0x74
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_RESET 0x0
typedef struct {
    uint32_t TENS_0_DIM : 16; // row size
    uint32_t TENS_1_DIM : 16; // column size
} csr_cnn_accel_tens_trans_lin_dims_res_reg_t;

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG.TENS_0_DIM - row size
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_MASK 0xffff
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG.TENS_1_DIM - column size
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_LSB 16
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_MASK 0xffff0000
#define CSR_CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG - tensor trans. convolution dimensions
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR 0x78
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_RESET 0x0
typedef struct {
    uint32_t TENS_0_DIM : 16; // row size
    uint32_t TENS_1_DIM : 16; // column size
} csr_cnn_accel_tens_trans_conv_dims_src_a_0_reg_t;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG.TENS_0_DIM - row size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_MASK 0xffff
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG.TENS_1_DIM - column size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_LSB 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_MASK 0xffff0000
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG - tensor trans. convolution dimensions
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR 0x7c
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_RESET 0x0
typedef struct {
    uint32_t TENS_2_DIM : 16; // row size
    uint32_t TENS_3_DIM : 16; // column size
} csr_cnn_accel_tens_trans_conv_dims_src_a_1_reg_t;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG.TENS_2_DIM - row size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_MASK 0xffff
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG.TENS_3_DIM - column size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_LSB 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_MASK 0xffff0000
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG - tensor trans. convolution dimensions
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR 0x80
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_RESET 0x0
typedef struct {
    uint32_t TENS_0_DIM : 16; // row size
    uint32_t TENS_1_DIM : 16; // column size
} csr_cnn_accel_tens_trans_conv_dims_src_b_0_reg_t;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG.TENS_0_DIM - row size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_MASK 0xffff
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG.TENS_1_DIM - column size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_LSB 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_MASK 0xffff0000
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG - tensor trans. convolution dimensions
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR 0x84
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_RESET 0x0
typedef struct {
    uint32_t TENS_2_DIM : 16; // row size
    uint32_t TENS_3_DIM : 16; // column size
} csr_cnn_accel_tens_trans_conv_dims_src_b_1_reg_t;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG.TENS_2_DIM - row size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_MASK 0xffff
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG.TENS_3_DIM - column size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_LSB 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_MASK 0xffff0000
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG - tensor trans. convolution dimensions
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR 0x88
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_RESET 0x0
typedef struct {
    uint32_t TENS_0_DIM : 16; // row size
    uint32_t TENS_1_DIM : 16; // column size
} csr_cnn_accel_tens_trans_conv_dims_res_0_reg_t;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG.TENS_0_DIM - row size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_MASK 0xffff
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG.TENS_1_DIM - column size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_LSB 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_MASK 0xffff0000
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG - tensor trans. convolution dimensions
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR 0x8c
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_RESET 0x0
typedef struct {
    uint32_t TENS_2_DIM : 16; // row size
    uint32_t TENS_3_DIM : 16; // column size
} csr_cnn_accel_tens_trans_conv_dims_res_1_reg_t;

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG.TENS_2_DIM - row size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_LSB 0
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_MASK 0xffff
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_RESET 0x0

// CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG.TENS_3_DIM - column size
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_WIDTH 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_LSB 16
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_MASK 0xffff0000
#define CSR_CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_RESET 0x0


// Register map structure
typedef struct {
    union {
        __IO uint32_t CNN_ACCEL_CTRL_REG; // main control register
        __IO csr_cnn_accel_ctrl_reg_t CNN_ACCEL_CTRL_REG_bf; // Bit access for CNN_ACCEL_CTRL_REG register
    };
    union {
        __I uint32_t CNN_ACCEL_STAT_REG; // main status register
        __I csr_cnn_accel_stat_reg_t CNN_ACCEL_STAT_REG_bf; // Bit access for CNN_ACCEL_STAT_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_INT_REG; // main interrupt register, reserved for future use, currently only registers implemented
        __IO csr_cnn_accel_int_reg_t CNN_ACCEL_INT_REG_bf; // Bit access for CNN_ACCEL_INT_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_MMEM_OFFSET_REG; // address offset for the main memory access, reserved for future use, currently only registers implemented
        __IO csr_cnn_accel_mmem_offset_reg_t CNN_ACCEL_MMEM_OFFSET_REG_bf; // Bit access for CNN_ACCEL_MMEM_OFFSET_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_GP_RW_REG; // general purpose read-write register, reserved for future use
        __IO csr_cnn_accel_gp_rw_reg_t CNN_ACCEL_GP_RW_REG_bf; // Bit access for CNN_ACCEL_GP_RW_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_PERF_RUN_CTRL_REG; // performance counter - total run cycles - control register
        __IO csr_cnn_accel_perf_run_ctrl_reg_t CNN_ACCEL_PERF_RUN_CTRL_REG_bf; // Bit access for CNN_ACCEL_PERF_RUN_CTRL_REG register
    };
    union {
        __I uint32_t CNN_ACCEL_PERF_RUN_LH_REG; // performance counter - run cycles - lower half
        __I csr_cnn_accel_perf_run_lh_reg_t CNN_ACCEL_PERF_RUN_LH_REG_bf; // Bit access for CNN_ACCEL_PERF_RUN_LH_REG register
    };
    union {
        __I uint32_t CNN_ACCEL_PERF_RUN_UH_REG; // performance counter - run cycles - upper half
        __I csr_cnn_accel_perf_run_uh_reg_t CNN_ACCEL_PERF_RUN_UH_REG_bf; // Bit access for CNN_ACCEL_PERF_RUN_UH_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_PERF_COMP_CTRL_REG; // performance counter - computation cycles - control register
        __IO csr_cnn_accel_perf_comp_ctrl_reg_t CNN_ACCEL_PERF_COMP_CTRL_REG_bf; // Bit access for CNN_ACCEL_PERF_COMP_CTRL_REG register
    };
    union {
        __I uint32_t CNN_ACCEL_PERF_COMP_LH_REG; // performance counter - run cycles - lower half
        __I csr_cnn_accel_perf_comp_lh_reg_t CNN_ACCEL_PERF_COMP_LH_REG_bf; // Bit access for CNN_ACCEL_PERF_COMP_LH_REG register
    };
    union {
        __I uint32_t CNN_ACCEL_PERF_COMP_UH_REG; // performance counter - run cycles - upper half
        __I csr_cnn_accel_perf_comp_uh_reg_t CNN_ACCEL_PERF_COMP_UH_REG_bf; // Bit access for CNN_ACCEL_PERF_COMP_UH_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG; // performance counter - stream C2H cycles - control register
        __IO csr_cnn_accel_perf_stream_c2h_ctrl_reg_t CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_bf; // Bit access for CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG register
    };
    union {
        __I uint32_t CNN_ACCEL_PERF_STREAM_C2H_LH_REG; // performance counter - run cycles - lower half
        __I csr_cnn_accel_perf_stream_c2h_lh_reg_t CNN_ACCEL_PERF_STREAM_C2H_LH_REG_bf; // Bit access for CNN_ACCEL_PERF_STREAM_C2H_LH_REG register
    };
    union {
        __I uint32_t CNN_ACCEL_PERF_STREAM_C2H_UH_REG; // performance counter - run cycles - upper half
        __I csr_cnn_accel_perf_stream_c2h_uh_reg_t CNN_ACCEL_PERF_STREAM_C2H_UH_REG_bf; // Bit access for CNN_ACCEL_PERF_STREAM_C2H_UH_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG; // performance counter - stream H2C cycles - control register
        __IO csr_cnn_accel_perf_stream_h2c_ctrl_reg_t CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_bf; // Bit access for CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG register
    };
    union {
        __I uint32_t CNN_ACCEL_PERF_STREAM_H2C_LH_REG; // performance counter - run cycles - lower half
        __I csr_cnn_accel_perf_stream_h2c_lh_reg_t CNN_ACCEL_PERF_STREAM_H2C_LH_REG_bf; // Bit access for CNN_ACCEL_PERF_STREAM_H2C_LH_REG register
    };
    union {
        __I uint32_t CNN_ACCEL_PERF_STREAM_H2C_UH_REG; // performance counter - run cycles - upper half
        __I csr_cnn_accel_perf_stream_h2c_uh_reg_t CNN_ACCEL_PERF_STREAM_H2C_UH_REG_bf; // Bit access for CNN_ACCEL_PERF_STREAM_H2C_UH_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG; // performance counter - cache stall - control register, reserved for future use, currently only registers implemented
        __IO csr_cnn_accel_perf_cache_stall_ctrl_reg_t CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_bf; // Bit access for CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG register
    };
    union {
        __I uint32_t CNN_ACCEL_PERF_CACHE_STALL_LH_REG; // performance counter - run cycles - lower half, reserved for future use, currently only registers implemented
        __I csr_cnn_accel_perf_cache_stall_lh_reg_t CNN_ACCEL_PERF_CACHE_STALL_LH_REG_bf; // Bit access for CNN_ACCEL_PERF_CACHE_STALL_LH_REG register
    };
    union {
        __I uint32_t CNN_ACCEL_PERF_CACHE_STALL_UH_REG; // performance counter - run cycles - upper half, reserved for future use, currently only registers implemented
        __I csr_cnn_accel_perf_cache_stall_uh_reg_t CNN_ACCEL_PERF_CACHE_STALL_UH_REG_bf; // Bit access for CNN_ACCEL_PERF_CACHE_STALL_UH_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_CFG_REG; // tensor trans. configuration
        __IO csr_cnn_accel_tens_trans_cfg_reg_t CNN_ACCEL_TENS_TRANS_CFG_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_CFG_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_CONV_CFG_REG; // convolution configuration
        __IO csr_cnn_accel_tens_trans_conv_cfg_reg_t CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_CONV_CFG_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG; // tensor start address
        __IO csr_cnn_accel_tens_trans_addr_src_a_reg_t CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG; // tensor start address
        __IO csr_cnn_accel_tens_trans_addr_src_b_reg_t CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG; // tensor start address
        __IO csr_cnn_accel_tens_trans_addr_batch_norm_reg_t CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG; // tensor start address
        __IO csr_cnn_accel_tens_trans_addr_bias_reg_t CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_ADDR_RES_REG; // tensor start address
        __IO csr_cnn_accel_tens_trans_addr_res_reg_t CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_ADDR_RES_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG; // tensor trans. linear (matrix) dimensions
        __IO csr_cnn_accel_tens_trans_lin_dims_src_a_reg_t CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG; // tensor trans. linear (matrix) dimensions
        __IO csr_cnn_accel_tens_trans_lin_dims_src_b_reg_t CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG; // tensor trans. linear (matrix) dimensions
        __IO csr_cnn_accel_tens_trans_lin_dims_res_reg_t CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG; // tensor trans. convolution dimensions
        __IO csr_cnn_accel_tens_trans_conv_dims_src_a_0_reg_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG; // tensor trans. convolution dimensions
        __IO csr_cnn_accel_tens_trans_conv_dims_src_a_1_reg_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG; // tensor trans. convolution dimensions
        __IO csr_cnn_accel_tens_trans_conv_dims_src_b_0_reg_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG; // tensor trans. convolution dimensions
        __IO csr_cnn_accel_tens_trans_conv_dims_src_b_1_reg_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG; // tensor trans. convolution dimensions
        __IO csr_cnn_accel_tens_trans_conv_dims_res_0_reg_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG register
    };
    union {
        __IO uint32_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG; // tensor trans. convolution dimensions
        __IO csr_cnn_accel_tens_trans_conv_dims_res_1_reg_t CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_bf; // Bit access for CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG register
    };
} csr_t;

#define CSR ((csr_t*)(CSR_BASE_ADDR))

#ifdef __cplusplus
}
#endif

#endif /* __CNN_ACCEL_REGMAP_H */