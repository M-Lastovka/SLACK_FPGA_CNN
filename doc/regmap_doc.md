# Register map

Created with [Corsair](https://github.com/esynr3z/corsair) v1.0.4.

## Conventions

| Access mode | Description               |
| :---------- | :------------------------ |
| rw          | Read and Write            |
| rw1c        | Read and Write 1 to Clear |
| rw1s        | Read and Write 1 to Set   |
| ro          | Read Only                 |
| roc         | Read Only to Clear        |
| roll        | Read Only / Latch Low     |
| rolh        | Read Only / Latch High    |
| wo          | Write only                |
| wosc        | Write Only / Self Clear   |

## Register map summary

Base address: 0x00000000

| Name                     | Address    | Description |
| :---                     | :---       | :---        |
| [CNN_ACCEL_CTRL_REG](#cnn_accel_ctrl_reg) | 0x00000000 | main control register |
| [CNN_ACCEL_STAT_REG](#cnn_accel_stat_reg) | 0x00000004 | main status register |
| [CNN_ACCEL_INT_REG](#cnn_accel_int_reg) | 0x00000008 | main interrupt register, reserved for future use, currently only registers implemented |
| [CNN_ACCEL_MMEM_OFFSET_REG](#cnn_accel_mmem_offset_reg) | 0x0000000c | address offset for the main memory access, reserved for future use, currently only registers implemented |
| [CNN_ACCEL_GP_RW_REG](#cnn_accel_gp_rw_reg) | 0x00000010 | general purpose read-write register, reserved for future use |
| [CNN_ACCEL_PERF_RUN_CTRL_REG](#cnn_accel_perf_run_ctrl_reg) | 0x00000014 | performance counter - total run cycles - control register |
| [CNN_ACCEL_PERF_RUN_LH_REG](#cnn_accel_perf_run_lh_reg) | 0x00000018 | performance counter - run cycles - lower half |
| [CNN_ACCEL_PERF_RUN_UH_REG](#cnn_accel_perf_run_uh_reg) | 0x0000001c | performance counter - run cycles - upper half |
| [CNN_ACCEL_PERF_COMP_CTRL_REG](#cnn_accel_perf_comp_ctrl_reg) | 0x00000020 | performance counter - computation cycles - control register |
| [CNN_ACCEL_PERF_COMP_LH_REG](#cnn_accel_perf_comp_lh_reg) | 0x00000024 | performance counter - run cycles - lower half |
| [CNN_ACCEL_PERF_COMP_UH_REG](#cnn_accel_perf_comp_uh_reg) | 0x00000028 | performance counter - run cycles - upper half |
| [CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG](#cnn_accel_perf_stream_c2h_ctrl_reg) | 0x0000002c | performance counter - stream C2H cycles - control register |
| [CNN_ACCEL_PERF_STREAM_C2H_LH_REG](#cnn_accel_perf_stream_c2h_lh_reg) | 0x00000030 | performance counter - run cycles - lower half |
| [CNN_ACCEL_PERF_STREAM_C2H_UH_REG](#cnn_accel_perf_stream_c2h_uh_reg) | 0x00000034 | performance counter - run cycles - upper half |
| [CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG](#cnn_accel_perf_stream_h2c_ctrl_reg) | 0x00000038 | performance counter - stream H2C cycles - control register |
| [CNN_ACCEL_PERF_STREAM_H2C_LH_REG](#cnn_accel_perf_stream_h2c_lh_reg) | 0x0000003c | performance counter - run cycles - lower half |
| [CNN_ACCEL_PERF_STREAM_H2C_UH_REG](#cnn_accel_perf_stream_h2c_uh_reg) | 0x00000040 | performance counter - run cycles - upper half |
| [CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG](#cnn_accel_perf_cache_stall_ctrl_reg) | 0x00000044 | performance counter - cache stall - control register, reserved for future use, currently only registers implemented |
| [CNN_ACCEL_PERF_CACHE_STALL_LH_REG](#cnn_accel_perf_cache_stall_lh_reg) | 0x00000048 | performance counter - run cycles - lower half, reserved for future use, currently only registers implemented |
| [CNN_ACCEL_PERF_CACHE_STALL_UH_REG](#cnn_accel_perf_cache_stall_uh_reg) | 0x0000004c | performance counter - run cycles - upper half, reserved for future use, currently only registers implemented |
| [CNN_ACCEL_TENS_TRANS_CFG_REG](#cnn_accel_tens_trans_cfg_reg) | 0x00000050 | tensor trans. configuration |
| [CNN_ACCEL_TENS_TRANS_CONV_CFG_REG](#cnn_accel_tens_trans_conv_cfg_reg) | 0x00000054 | convolution configuration |
| [CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG](#cnn_accel_tens_trans_addr_src_a_reg) | 0x00000058 | tensor start address |
| [CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG](#cnn_accel_tens_trans_addr_src_b_reg) | 0x0000005c | tensor start address |
| [CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG](#cnn_accel_tens_trans_addr_batch_norm_reg) | 0x00000060 | tensor start address |
| [CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG](#cnn_accel_tens_trans_addr_bias_reg) | 0x00000064 | tensor start address |
| [CNN_ACCEL_TENS_TRANS_ADDR_RES_REG](#cnn_accel_tens_trans_addr_res_reg) | 0x00000068 | tensor start address |
| [CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG](#cnn_accel_tens_trans_lin_dims_src_a_reg) | 0x0000006c | tensor trans. linear (matrix) dimensions |
| [CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG](#cnn_accel_tens_trans_lin_dims_src_b_reg) | 0x00000070 | tensor trans. linear (matrix) dimensions |
| [CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG](#cnn_accel_tens_trans_lin_dims_res_reg) | 0x00000074 | tensor trans. linear (matrix) dimensions |
| [CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG](#cnn_accel_tens_trans_conv_dims_src_a_0_reg) | 0x00000078 | tensor trans. convolution dimensions |
| [CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG](#cnn_accel_tens_trans_conv_dims_src_a_1_reg) | 0x0000007c | tensor trans. convolution dimensions |
| [CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG](#cnn_accel_tens_trans_conv_dims_src_b_0_reg) | 0x00000080 | tensor trans. convolution dimensions |
| [CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG](#cnn_accel_tens_trans_conv_dims_src_b_1_reg) | 0x00000084 | tensor trans. convolution dimensions |
| [CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG](#cnn_accel_tens_trans_conv_dims_res_0_reg) | 0x00000088 | tensor trans. convolution dimensions |
| [CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG](#cnn_accel_tens_trans_conv_dims_res_1_reg) | 0x0000008c | tensor trans. convolution dimensions |

## CNN_ACCEL_CTRL_REG

main control register

Address offset: 0x00000000

Reset value: 0x00000000

![cnn_accel_ctrl_reg](md_img/cnn_accel_ctrl_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| -                | 31:12  | -               | 0x00000    | Reserved |
| SOFT_RESET       | 11     | wosc            | 0x0        | global software reset, active high |
| TENS_TRANS_SEQ_LEN | 10:1   | rw              | 0x00       | number of operations in the tensor trans. sequence to be executed |
| TENS_TRANS_SEQ_START | 0      | wosc            | 0x0        | start signal to execute the tensor trans. sequence |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_STAT_REG

main status register

Address offset: 0x00000004

Reset value: 0x00000000

![cnn_accel_stat_reg](md_img/cnn_accel_stat_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| -                | 31:11  | -               | 0x00000    | Reserved |
| TENS_TRANS_SEQ_CNT | 10:1   | ro              | 0x00       | index of the current trans. sequence in progress |
| TENS_TRANS_SEQ_BUSY | 0      | ro              | 0x0        | active high if tensor trans. sequence is progressing |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_INT_REG

main interrupt register, reserved for future use, currently only registers implemented

Address offset: 0x00000008

Reset value: 0x00000000

![cnn_accel_int_reg](md_img/cnn_accel_int_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| -                | 31:9   | -               | 0x00000    | Reserved |
| INT_STREAM_C2H_DONE_CLEAR | 8      | wosc            | 0x0        | interrupt clear - tensor transformation sequence done |
| INT_STREAM_C2H_DONE_STAT | 7      | ro              | 0x0        | interrupt status - tensor transformation sequence done |
| INT_STREAM_C2H_DONE_EN | 6      | rw              | 0x0        | interrupt enable - tensor transformation sequence done |
| INT_STREAM_H2C_DONE_CLEAR | 5      | wosc            | 0x0        | interrupt clear - tensor transformation sequence done |
| INT_STREAM_H2C_DONE_STAT | 4      | ro              | 0x0        | interrupt status - tensor transformation sequence done |
| INT_STREAM_H2C_DONE_EN | 3      | rw              | 0x0        | interrupt enable - tensor transformation sequence done |
| INT_TENS_TRANS_SEQ_DONE_CLEAR | 2      | wosc            | 0x0        | interrupt clear - tensor transformation sequence done |
| INT_TENS_TRANS_SEQ_DONE_STAT | 1      | ro              | 0x0        | interrupt status - tensor transformation sequence done |
| INT_TENS_TRANS_SEQ_DONE_EN | 0      | rw              | 0x0        | interrupt enable - tensor transformation sequence done |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_MMEM_OFFSET_REG

address offset for the main memory access, reserved for future use, currently only registers implemented

Address offset: 0x0000000c

Reset value: 0x00000000

![cnn_accel_mmem_offset_reg](md_img/cnn_accel_mmem_offset_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| MMEM_BASE_ADDR   | 31:0   | rw              | 0x00000000 | base address value |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_GP_RW_REG

general purpose read-write register, reserved for future use

Address offset: 0x00000010

Reset value: 0x00000000

![cnn_accel_gp_rw_reg](md_img/cnn_accel_gp_rw_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| GP_RW            | 31:0   | rw              | 0x00000000 | general purpose register |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_RUN_CTRL_REG

performance counter - total run cycles - control register

Address offset: 0x00000014

Reset value: 0x00000000

![cnn_accel_perf_run_ctrl_reg](md_img/cnn_accel_perf_run_ctrl_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| -                | 31:2   | -               | 0x0000000  | Reserved |
| PERF_RUN_CLEAR   | 1      | wosc            | 0x0        | perf. counter clear |
| PERF_RUN_EN      | 0      | rw              | 0x0        | perf. counter enable |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_RUN_LH_REG

performance counter - run cycles - lower half

Address offset: 0x00000018

Reset value: 0x00000000

![cnn_accel_perf_run_lh_reg](md_img/cnn_accel_perf_run_lh_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| PERF_RUN_LH      | 31:0   | ro              | 0x00000000 | perf. counter value |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_RUN_UH_REG

performance counter - run cycles - upper half

Address offset: 0x0000001c

Reset value: 0x00000000

![cnn_accel_perf_run_uh_reg](md_img/cnn_accel_perf_run_uh_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| PERF_RUN_UH      | 31:0   | ro              | 0x00000000 | perf. counter value |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_COMP_CTRL_REG

performance counter - computation cycles - control register

Address offset: 0x00000020

Reset value: 0x00000000

![cnn_accel_perf_comp_ctrl_reg](md_img/cnn_accel_perf_comp_ctrl_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| -                | 31:2   | -               | 0x0000000  | Reserved |
| PERF_COMP_CLEAR  | 1      | wosc            | 0x0        | perf. counter clear |
| PERF_COMP_EN     | 0      | rw              | 0x0        | perf. counter enable |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_COMP_LH_REG

performance counter - run cycles - lower half

Address offset: 0x00000024

Reset value: 0x00000000

![cnn_accel_perf_comp_lh_reg](md_img/cnn_accel_perf_comp_lh_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| PERF_COMP_LH     | 31:0   | ro              | 0x00000000 | perf. counter value |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_COMP_UH_REG

performance counter - run cycles - upper half

Address offset: 0x00000028

Reset value: 0x00000000

![cnn_accel_perf_comp_uh_reg](md_img/cnn_accel_perf_comp_uh_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| PERF_COMP_UH     | 31:0   | ro              | 0x00000000 | perf. counter value |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG

performance counter - stream C2H cycles - control register

Address offset: 0x0000002c

Reset value: 0x00000000

![cnn_accel_perf_stream_c2h_ctrl_reg](md_img/cnn_accel_perf_stream_c2h_ctrl_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| -                | 31:2   | -               | 0x0000000  | Reserved |
| PERF_STREAM_CLEAR | 1      | wosc            | 0x0        | perf. counter clear |
| PERF_STREAM_EN   | 0      | rw              | 0x0        | perf. counter enable |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_STREAM_C2H_LH_REG

performance counter - run cycles - lower half

Address offset: 0x00000030

Reset value: 0x00000000

![cnn_accel_perf_stream_c2h_lh_reg](md_img/cnn_accel_perf_stream_c2h_lh_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| PERF_STREAM_LH   | 31:0   | ro              | 0x00000000 | perf. counter value |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_STREAM_C2H_UH_REG

performance counter - run cycles - upper half

Address offset: 0x00000034

Reset value: 0x00000000

![cnn_accel_perf_stream_c2h_uh_reg](md_img/cnn_accel_perf_stream_c2h_uh_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| PERF_STREAM_UH   | 31:0   | ro              | 0x00000000 | perf. counter value |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG

performance counter - stream H2C cycles - control register

Address offset: 0x00000038

Reset value: 0x00000000

![cnn_accel_perf_stream_h2c_ctrl_reg](md_img/cnn_accel_perf_stream_h2c_ctrl_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| -                | 31:2   | -               | 0x0000000  | Reserved |
| PERF_STREAM_CLEAR | 1      | wosc            | 0x0        | perf. counter clear |
| PERF_STREAM_EN   | 0      | rw              | 0x0        | perf. counter enable |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_STREAM_H2C_LH_REG

performance counter - run cycles - lower half

Address offset: 0x0000003c

Reset value: 0x00000000

![cnn_accel_perf_stream_h2c_lh_reg](md_img/cnn_accel_perf_stream_h2c_lh_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| PERF_STREAM_LH   | 31:0   | ro              | 0x00000000 | perf. counter value |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_STREAM_H2C_UH_REG

performance counter - run cycles - upper half

Address offset: 0x00000040

Reset value: 0x00000000

![cnn_accel_perf_stream_h2c_uh_reg](md_img/cnn_accel_perf_stream_h2c_uh_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| PERF_STREAM_UH   | 31:0   | ro              | 0x00000000 | perf. counter value |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG

performance counter - cache stall - control register, reserved for future use, currently only registers implemented

Address offset: 0x00000044

Reset value: 0x00000000

![cnn_accel_perf_cache_stall_ctrl_reg](md_img/cnn_accel_perf_cache_stall_ctrl_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| -                | 31:2   | -               | 0x0000000  | Reserved |
| PERF_STREAM_CLEAR | 1      | wosc            | 0x0        | perf. counter clear |
| PERF_STREAM_EN   | 0      | rw              | 0x0        | perf. counter enable |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_CACHE_STALL_LH_REG

performance counter - run cycles - lower half, reserved for future use, currently only registers implemented

Address offset: 0x00000048

Reset value: 0x00000000

![cnn_accel_perf_cache_stall_lh_reg](md_img/cnn_accel_perf_cache_stall_lh_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| PERF_STREAM_LH   | 31:0   | ro              | 0x00000000 | perf. counter value |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_PERF_CACHE_STALL_UH_REG

performance counter - run cycles - upper half, reserved for future use, currently only registers implemented

Address offset: 0x0000004c

Reset value: 0x00000000

![cnn_accel_perf_cache_stall_uh_reg](md_img/cnn_accel_perf_cache_stall_uh_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| PERF_STREAM_UH   | 31:0   | ro              | 0x00000000 | perf. counter value |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_CFG_REG

tensor trans. configuration

Address offset: 0x00000050

Reset value: 0x00000000

![cnn_accel_tens_trans_cfg_reg](md_img/cnn_accel_tens_trans_cfg_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| -                | 31:11  | -               | 0x00000    | Reserved |
| BIAS_EN          | 10     | rw              | 0x0        | bias enable |
| REPL_BIAS        | 9      | rw              | 0x0        | replicate bias flag |
| BATCH_NORM_EN    | 8      | rw              | 0x0        | batch normalization enable |
| NLIN_F_TYPE      | 7:4    | rw              | 0x0        | nonlin. function type |
| TENS_TRANS_TYPE  | 3:0    | rw              | 0x0        | tensor trans. type |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_CONV_CFG_REG

convolution configuration

Address offset: 0x00000054

Reset value: 0x00000000

![cnn_accel_tens_trans_conv_cfg_reg](md_img/cnn_accel_tens_trans_conv_cfg_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| CONV_PADDING_1   | 31:24  | rw              | 0x00       | convolution zero padding |
| CONV_PADDING_0   | 23:16  | rw              | 0x00       | convolution zero padding |
| CONV_STRIDE_1    | 15:8   | rw              | 0x00       | convolution stride |
| CONV_STRIDE_0    | 7:0    | rw              | 0x00       | convolution stride |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG

tensor start address

Address offset: 0x00000058

Reset value: 0x00000000

![cnn_accel_tens_trans_addr_src_a_reg](md_img/cnn_accel_tens_trans_addr_src_a_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_ADDR        | 31:0   | rw              | 0x00000000 | tensor address |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG

tensor start address

Address offset: 0x0000005c

Reset value: 0x00000000

![cnn_accel_tens_trans_addr_src_b_reg](md_img/cnn_accel_tens_trans_addr_src_b_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_ADDR        | 31:0   | rw              | 0x00000000 | tensor address |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG

tensor start address

Address offset: 0x00000060

Reset value: 0x00000000

![cnn_accel_tens_trans_addr_batch_norm_reg](md_img/cnn_accel_tens_trans_addr_batch_norm_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_ADDR        | 31:0   | rw              | 0x00000000 | tensor address |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG

tensor start address

Address offset: 0x00000064

Reset value: 0x00000000

![cnn_accel_tens_trans_addr_bias_reg](md_img/cnn_accel_tens_trans_addr_bias_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_ADDR        | 31:0   | rw              | 0x00000000 | tensor address |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_ADDR_RES_REG

tensor start address

Address offset: 0x00000068

Reset value: 0x00000000

![cnn_accel_tens_trans_addr_res_reg](md_img/cnn_accel_tens_trans_addr_res_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_ADDR        | 31:0   | rw              | 0x00000000 | tensor address |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG

tensor trans. linear (matrix) dimensions

Address offset: 0x0000006c

Reset value: 0x00000000

![cnn_accel_tens_trans_lin_dims_src_a_reg](md_img/cnn_accel_tens_trans_lin_dims_src_a_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_1_DIM       | 31:16  | rw              | 0x0000     | column size |
| TENS_0_DIM       | 15:0   | rw              | 0x0000     | row size |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG

tensor trans. linear (matrix) dimensions

Address offset: 0x00000070

Reset value: 0x00000000

![cnn_accel_tens_trans_lin_dims_src_b_reg](md_img/cnn_accel_tens_trans_lin_dims_src_b_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_1_DIM       | 31:16  | rw              | 0x0000     | column size |
| TENS_0_DIM       | 15:0   | rw              | 0x0000     | row size |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG

tensor trans. linear (matrix) dimensions

Address offset: 0x00000074

Reset value: 0x00000000

![cnn_accel_tens_trans_lin_dims_res_reg](md_img/cnn_accel_tens_trans_lin_dims_res_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_1_DIM       | 31:16  | rw              | 0x0000     | column size |
| TENS_0_DIM       | 15:0   | rw              | 0x0000     | row size |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG

tensor trans. convolution dimensions

Address offset: 0x00000078

Reset value: 0x00000000

![cnn_accel_tens_trans_conv_dims_src_a_0_reg](md_img/cnn_accel_tens_trans_conv_dims_src_a_0_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_1_DIM       | 31:16  | rw              | 0x0000     | column size |
| TENS_0_DIM       | 15:0   | rw              | 0x0000     | row size |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG

tensor trans. convolution dimensions

Address offset: 0x0000007c

Reset value: 0x00000000

![cnn_accel_tens_trans_conv_dims_src_a_1_reg](md_img/cnn_accel_tens_trans_conv_dims_src_a_1_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_3_DIM       | 31:16  | rw              | 0x0000     | column size |
| TENS_2_DIM       | 15:0   | rw              | 0x0000     | row size |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG

tensor trans. convolution dimensions

Address offset: 0x00000080

Reset value: 0x00000000

![cnn_accel_tens_trans_conv_dims_src_b_0_reg](md_img/cnn_accel_tens_trans_conv_dims_src_b_0_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_1_DIM       | 31:16  | rw              | 0x0000     | column size |
| TENS_0_DIM       | 15:0   | rw              | 0x0000     | row size |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG

tensor trans. convolution dimensions

Address offset: 0x00000084

Reset value: 0x00000000

![cnn_accel_tens_trans_conv_dims_src_b_1_reg](md_img/cnn_accel_tens_trans_conv_dims_src_b_1_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_3_DIM       | 31:16  | rw              | 0x0000     | column size |
| TENS_2_DIM       | 15:0   | rw              | 0x0000     | row size |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG

tensor trans. convolution dimensions

Address offset: 0x00000088

Reset value: 0x00000000

![cnn_accel_tens_trans_conv_dims_res_0_reg](md_img/cnn_accel_tens_trans_conv_dims_res_0_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_1_DIM       | 31:16  | rw              | 0x0000     | column size |
| TENS_0_DIM       | 15:0   | rw              | 0x0000     | row size |

Back to [Register map](#register-map-summary).

## CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG

tensor trans. convolution dimensions

Address offset: 0x0000008c

Reset value: 0x00000000

![cnn_accel_tens_trans_conv_dims_res_1_reg](md_img/cnn_accel_tens_trans_conv_dims_res_1_reg.svg)

| Name             | Bits   | Mode            | Reset      | Description |
| :---             | :---   | :---            | :---       | :---        |
| TENS_3_DIM       | 31:16  | rw              | 0x0000     | column size |
| TENS_2_DIM       | 15:0   | rw              | 0x0000     | row size |

Back to [Register map](#register-map-summary).
