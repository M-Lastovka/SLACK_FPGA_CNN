`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     regmap
// Project Name:    Efficient FPGA CNN implementation
// Description:     Register map
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import axi_if_pckg::*;
import regmap_pckg::*;
import regmap_reg_pckg::*;
import proc_pipe_pckg::*;
import perf_cnt_pckg::*;

module regmap
(
    //clk&reset
    input  logic clk,
    input  logic rst_n,
    output logic soft_rst,
    //control
    regmap_rd_if.regmap s_axil_regmap_rd_if,
    regmap_wr_if.regmap s_axil_regmap_wr_if,
    regmap_rd_if.regmap main_fsm_regmap_rd_if,
    input   logic [C_PERF_CNT_CNT-1:0]  perf_cnt_step_fsm,
    input   logic [C_TENS_TRANS_SEQ_CNT_WDT-1:0] tens_trans_seq_cnt,
    output  logic [C_TENS_TRANS_SEQ_CNT_WDT-1:0] tens_trans_seq_lim,
    block_ctrl_if.master                         main_fsm_s_ctrl_if
);

logic regmap_ram_lock; //RAM region is locked, i.e. writes have no effect, reads function as usual

typedef enum
{
    SEL_MEM_REG,
    SEL_MEM_RAM,
    SEL_MEM_NONE
} regmap_sel_t;

regmap_sel_t regmap_wr_mem_sel;
regmap_sel_t regmap_rd_mem_sel;
regmap_sel_t regmap_rd_mem_sel_i;

logic [C_REGMAP_INT_ADDR_WDT-1:0] regmap_wr_addr;
logic regmap_wr_en;
logic [C_REGMAP_DATA_WDT-1:0] regmap_wr_data;
logic [C_REGMAP_STRB_WDT-1:0] regmap_wr_strb;

logic [C_REGMAP_INT_ADDR_WDT-1:0] regmap_rd_addr;
logic regmap_rd_en;

//REG region

logic [C_REGMAP_REG_INT_ADDR_WDT-1:0] regmap_reg_wr_addr_q;
logic regmap_reg_wr_en_q;
logic [C_REGMAP_DATA_WDT-1:0] regmap_reg_wr_data_q;
logic [C_REGMAP_STRB_WDT-1:0] regmap_reg_wr_strb_q;

logic [C_REGMAP_REG_INT_ADDR_WDT-1:0] regmap_reg_rd_addr_q;
logic regmap_reg_rd_en_q;

logic [C_REGMAP_REG_INT_ADDR_WDT-1:0] regmap_reg_wr_addr;
logic regmap_reg_wr_en;
logic [C_REGMAP_DATA_WDT-1:0] regmap_reg_wr_data;
logic [C_REGMAP_STRB_WDT-1:0] regmap_reg_wr_strb;

logic [C_REGMAP_REG_INT_ADDR_WDT-1:0] regmap_reg_rd_addr;
logic regmap_reg_rd_en;
logic regmap_reg_rd_en_i;
logic [C_REGMAP_DATA_WDT-1:0] regmap_reg_rd_data;


//RAM region
logic [C_REGMAP_RAM_INT_ADDR_WDT-1:0] regmap_ram_wr_addr_q;
logic regmap_ram_wr_en_q;
logic [C_REGMAP_DATA_WDT-1:0] regmap_ram_wr_data_q;
logic [C_REGMAP_STRB_WDT-1:0] regmap_ram_wr_strb_q;

logic [C_REGMAP_RAM_INT_ADDR_WDT-1:0] regmap_ram_rd_addr_q;
logic regmap_ram_rd_en_q;

logic [C_REGMAP_RAM_INT_ADDR_WDT-1:0] regmap_ram_wr_addr;
logic regmap_ram_wr_en;
logic [C_REGMAP_DATA_WDT-1:0] regmap_ram_wr_data;
logic [C_REGMAP_STRB_WDT-1:0] regmap_ram_wr_strb;

logic [C_REGMAP_RAM_INT_ADDR_WDT-1:0] regmap_ram_rd_addr;
logic regmap_ram_rd_en;
logic regmap_ram_rd_en_i;
logic [C_REGMAP_DATA_WDT-1:0] regmap_ram_rd_data;

logic s_axil_regmap_rd_if_rd_en_i;
logic main_fsm_regmap_rd_if_rd_en_i;

//select between the interfaces
always_comb begin : rd_wr_if_sel_proc
    regmap_wr_addr = s_axil_regmap_wr_if.wr_addr >> 2;
    regmap_wr_en   = s_axil_regmap_wr_if.wr_en;
    regmap_wr_data = s_axil_regmap_wr_if.wr_data;
    regmap_wr_strb = s_axil_regmap_wr_if.wr_strb;

    if(main_fsm_regmap_rd_if.rd_en) begin
        regmap_rd_addr = main_fsm_regmap_rd_if.rd_addr >> 2;
        regmap_rd_en   = main_fsm_regmap_rd_if.rd_en;
    end else if(s_axil_regmap_rd_if.rd_en) begin
        regmap_rd_addr = s_axil_regmap_rd_if.rd_addr >> 2;
        regmap_rd_en   = s_axil_regmap_rd_if.rd_en;
    end else begin
        regmap_rd_addr = '0;
        regmap_rd_en   = 1'b0;
    end
end

//memory region select
always_comb begin : mem_reg_sel_comb_proc
    if(regmap_rd_addr >= C_REGMAP_REG_START_ADDR >> 2 & regmap_rd_addr <= C_REGMAP_REG_END_ADDR >> 2)
        regmap_rd_mem_sel = SEL_MEM_REG;
    else if(regmap_rd_addr >= C_REGMAP_RAM_START_ADDR >> 2 & regmap_rd_addr <= C_REGMAP_RAM_END_ADDR >> 2)
        regmap_rd_mem_sel = SEL_MEM_RAM;
    else
        regmap_rd_mem_sel = SEL_MEM_NONE;

    if(regmap_wr_addr >= C_REGMAP_REG_START_ADDR >> 2 & regmap_wr_addr <= C_REGMAP_REG_END_ADDR >> 2)
        regmap_wr_mem_sel = SEL_MEM_REG;
    else if(regmap_wr_addr >= C_REGMAP_RAM_START_ADDR >> 2 & regmap_wr_addr <= C_REGMAP_RAM_END_ADDR >> 2 & (!regmap_ram_lock | main_fsm_regmap_rd_if.rd_en))
        regmap_wr_mem_sel = SEL_MEM_RAM;
    else
        regmap_wr_mem_sel = SEL_MEM_NONE;
end

//apply offsets, activate reads/writes enables
always_comb begin : access_comp_proc
    //REG region
    regmap_reg_wr_addr_q  = '0;
    regmap_reg_wr_en_q    = 1'b0;
    regmap_reg_wr_data_q  = '0;
    regmap_reg_wr_strb_q  = '0;
    regmap_reg_rd_addr_q  = '0;
    regmap_reg_rd_en_q    = 1'b0;
    regmap_ram_wr_addr_q  = '0;
    regmap_ram_wr_en_q    = 1'b0;
    regmap_ram_wr_data_q  = '0;
    regmap_ram_wr_strb_q  = '0;
    regmap_ram_rd_addr_q  = '0;
    regmap_ram_rd_en_q    = 1'b0;

    if(regmap_rd_mem_sel == SEL_MEM_REG) begin
        regmap_reg_rd_addr_q  = regmap_rd_addr - (C_REGMAP_REG_START_ADDR >> 2);
        regmap_reg_rd_en_q    = regmap_rd_en;
    end else if(regmap_rd_mem_sel == SEL_MEM_RAM) begin
        regmap_ram_rd_addr_q  = regmap_rd_addr - (C_REGMAP_RAM_START_ADDR >> 2);
        regmap_ram_rd_en_q    = regmap_rd_en;
    end

    if(regmap_wr_mem_sel == SEL_MEM_REG) begin
        regmap_reg_wr_addr_q  = regmap_wr_addr - (C_REGMAP_REG_START_ADDR >> 2);
        regmap_reg_wr_en_q    = regmap_wr_en;
        regmap_reg_wr_data_q  = regmap_wr_data;
        regmap_reg_wr_strb_q  = regmap_wr_strb;
    end else if(regmap_wr_mem_sel == SEL_MEM_RAM) begin
        regmap_ram_wr_addr_q  = regmap_wr_addr - (C_REGMAP_RAM_START_ADDR >> 2);
        regmap_ram_wr_en_q    = regmap_wr_en;
        regmap_ram_wr_data_q  = regmap_wr_data;
        regmap_ram_wr_strb_q  = regmap_wr_strb;
    end
end

always_ff @(posedge clk) begin : regmap_mem_reg //simple register for all the regmap input signals (both RAM and REG region)
    if(!rst_n) begin
        regmap_reg_wr_addr  <= '0;
        regmap_reg_wr_en    <= 1'b0;
        regmap_reg_wr_data  <= '0;
        regmap_reg_wr_strb  <= '0;
        regmap_reg_rd_addr  <= '0;
        regmap_reg_rd_en    <= 1'b0;
        regmap_ram_wr_addr  <= '0;
        regmap_ram_wr_en    <= 1'b0;
        regmap_ram_wr_data  <= '0;
        regmap_ram_wr_strb  <= '0;
        regmap_ram_rd_addr  <= '0;
        regmap_ram_rd_en    <= 1'b0;
    end else begin
        regmap_reg_wr_addr  <= regmap_reg_wr_addr_q;
        regmap_reg_wr_en    <= regmap_reg_wr_en_q;
        regmap_reg_wr_data  <= regmap_reg_wr_data_q;
        regmap_reg_wr_strb  <= regmap_reg_wr_strb_q;
        regmap_reg_rd_addr  <= regmap_reg_rd_addr_q;
        regmap_reg_rd_en    <= regmap_reg_rd_en_q;
        regmap_ram_wr_addr  <= regmap_ram_wr_addr_q;
        regmap_ram_wr_en    <= regmap_ram_wr_en_q;
        regmap_ram_wr_data  <= regmap_ram_wr_data_q;
        regmap_ram_wr_strb  <= regmap_ram_wr_strb_q;
        regmap_ram_rd_addr  <= regmap_ram_rd_addr_q;
        regmap_ram_rd_en    <= regmap_ram_rd_en_q;
    end 
end

//-------------------------------------------------------------
//RAM region---------------------------------------------------
//-------------------------------------------------------------

logic [C_REGMAP_DATA_WDT-1:0] regmap_ram_mem[C_REGMAP_RAM_INT_SIZE-1:0];

initial begin
    foreach(regmap_ram_mem[i])
        regmap_ram_mem[i] = '0;
end

always_ff @(posedge clk) begin : regmap_ram_mem_proc
    if(regmap_ram_rd_en) begin
        regmap_ram_rd_data <= regmap_ram_mem[regmap_ram_rd_addr];
    end 

    if(regmap_ram_wr_en) begin
        foreach(regmap_ram_wr_strb[i]) begin
            regmap_ram_mem[regmap_ram_wr_addr][i*C_BYTE_WDT +: C_BYTE_WDT] <= regmap_ram_wr_data[i*C_BYTE_WDT +: C_BYTE_WDT];
        end
    end
end

always_ff @(posedge clk) begin : regmap_rd_data_sel_reg
    if(!rst_n) begin
        regmap_reg_rd_en_i  <= 1'b0;
        regmap_ram_rd_en_i  <= 1'b0;
    end else begin
        regmap_reg_rd_en_i  <= regmap_reg_rd_en;
        regmap_ram_rd_en_i  <= regmap_ram_rd_en;
    end 
end

del_chain //delay the read enables so that we know where to assign the read data
#(
    .IN_WORD_WDT(1),
    .DEL_CYC_LEN(C_REGMAP_CMD_CYC_LEN)
)
regmap_rd_if_en_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(1'b1),
    .in_word(s_axil_regmap_rd_if.rd_en),
    .in_word_val(main_fsm_regmap_rd_if.rd_en),
    .in_word_del(s_axil_regmap_rd_if_rd_en_i),
    .in_word_val_del(main_fsm_regmap_rd_if_rd_en_i)
);

logic main_fsm_regmap_rd_if_rd_val_i;
logic [C_REGMAP_DATA_WDT-1:0] main_fsm_regmap_rd_if_rd_data_i;
logic s_axil_regmap_rd_if_rd_val_i;
logic [C_REGMAP_DATA_WDT-1:0] s_axil_regmap_rd_if_rd_data_i;


//read data MUX
always_comb begin : rd_data_mux
    s_axil_regmap_rd_if_rd_data_i     = '0;
    main_fsm_regmap_rd_if_rd_data_i   = '0;
    s_axil_regmap_rd_if_rd_val_i      = 1'b0;
    main_fsm_regmap_rd_if_rd_val_i    = 1'b0;

    if(regmap_ram_rd_en_i) begin
        if(main_fsm_regmap_rd_if_rd_en_i) begin
            main_fsm_regmap_rd_if_rd_data_i = regmap_ram_rd_data;
            main_fsm_regmap_rd_if_rd_val_i  = 1'b1;
        end else if(s_axil_regmap_rd_if_rd_en_i) begin
            s_axil_regmap_rd_if_rd_data_i = regmap_ram_rd_data;
            s_axil_regmap_rd_if_rd_val_i  = 1'b1;
        end
    end else if(regmap_reg_rd_en_i)  begin
        if(main_fsm_regmap_rd_if_rd_en_i) begin
            main_fsm_regmap_rd_if_rd_data_i = regmap_reg_rd_data;
            main_fsm_regmap_rd_if_rd_val_i  = 1'b1;
        end else if(s_axil_regmap_rd_if_rd_en_i) begin
            s_axil_regmap_rd_if_rd_data_i = regmap_reg_rd_data;
            s_axil_regmap_rd_if_rd_val_i  = 1'b1;
        end
    end
end

del_chain 
#(
    .IN_WORD_WDT($bits(s_axil_regmap_rd_if_rd_data_i)),
    .DEL_CYC_LEN(C_MAIN_FSM_REGMAP_RD_IF_CYC_LEN)
)
main_fsm_regmap_rd_if_resp_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(1'b1),
    .in_word(main_fsm_regmap_rd_if_rd_data_i),
    .in_word_val(main_fsm_regmap_rd_if_rd_val_i),
    .in_word_del(main_fsm_regmap_rd_if.rd_data),
    .in_word_val_del(main_fsm_regmap_rd_if.rd_val)
);

del_chain 
#(
    .IN_WORD_WDT($bits(main_fsm_regmap_rd_if_rd_data_i)),
    .DEL_CYC_LEN(C_S_AXI_2REGMAP_DEL_CYC_LEN)
)
s_axil_regmap_rd_if_resp_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(1'b1),
    .in_word(s_axil_regmap_rd_if_rd_data_i),
    .in_word_val(s_axil_regmap_rd_if_rd_val_i),
    .in_word_del(s_axil_regmap_rd_if.rd_data),
    .in_word_val_del(s_axil_regmap_rd_if.rd_val)
);

//-------------------------------------------------------------
//REG region---------------------------------------------------
//-------------------------------------------------------------


//------------------------------------------------------------------------------
// [0x0] - CNN_ACCEL_CTRL_REG - main control register
//------------------------------------------------------------------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_ctrl_reg_rd_data;
assign csr_cnn_accel_ctrl_reg_rd_data[C_REGMAP_DATA_WDT-1:12] = 20'h0;

logic csr_cnn_accel_ctrl_reg_wen;
assign csr_cnn_accel_ctrl_reg_wen = regmap_reg_wr_en && (regmap_reg_wr_addr == C_CTRL_REG_ADDR >> 2);

logic csr_cnn_accel_ctrl_reg_ren;
assign csr_cnn_accel_ctrl_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_CTRL_REG_ADDR >> 2);
logic csr_cnn_accel_ctrl_reg_ren_ff;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_ctrl_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_ctrl_reg_ren_ff <= csr_cnn_accel_ctrl_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_CTRL_REG[0] - TENS_TRANS_SEQ_START - write to start the tensor trans. sequence, if enabled
// access: wosc, hardware: oa
//---------------------
logic  csr_cnn_accel_ctrl_reg_tens_trans_seq_start_ff;

assign csr_cnn_accel_ctrl_reg_rd_data[0] = 1'b0;


always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_ctrl_reg_tens_trans_seq_start_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_ctrl_reg_tens_trans_seq_start_ff <= regmap_reg_wr_data[0];
            end
        end else begin
            csr_cnn_accel_ctrl_reg_tens_trans_seq_start_ff <= 1'b0;
        end
    end
end

//---------------------
// Bit field:
// CNN_ACCEL_CTRL_REG[10:1] - TENS_TRANS_SEQ_LEN - length of the tensor trans. sequence
// access: rw, hardware: o
//---------------------
logic [9:0] csr_cnn_accel_ctrl_reg_tens_trans_seq_len_ff;

assign csr_cnn_accel_ctrl_reg_rd_data[10:1] = csr_cnn_accel_ctrl_reg_tens_trans_seq_len_ff;


always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_ctrl_reg_tens_trans_seq_len_ff <= 10'h0;
    end else  begin
     if (csr_cnn_accel_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_ctrl_reg_tens_trans_seq_len_ff[6:0] <= regmap_reg_wr_data[7:1];
            end
            if (regmap_reg_wr_strb[1]) begin
                csr_cnn_accel_ctrl_reg_tens_trans_seq_len_ff[9:7] <= regmap_reg_wr_data[10:8];
            end
        end else begin
            csr_cnn_accel_ctrl_reg_tens_trans_seq_len_ff <= csr_cnn_accel_ctrl_reg_tens_trans_seq_len_ff;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_CTRL_REG[11] - SOFT_RESET - software reset
// access: wosc, hardware: oa
//---------------------
logic  csr_cnn_accel_ctrl_reg_soft_reset_ff;

assign csr_cnn_accel_ctrl_reg_rd_data[11] = 1'b0;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_ctrl_reg_soft_reset_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[1]) begin
                csr_cnn_accel_ctrl_reg_soft_reset_ff <= regmap_reg_wr_data[11];
            end
        end else begin
            csr_cnn_accel_ctrl_reg_soft_reset_ff <= 1'b0;
        end
    end
end


//------------------------------------------------------------------------------
// CSR:
// [0x4] - CNN_ACCEL_STAT_REG - main status register
//------------------------------------------------------------------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_stat_reg_rd_data;
assign csr_cnn_accel_stat_reg_rd_data[C_REGMAP_DATA_WDT-1:11] = 21'h0;


logic csr_cnn_accel_stat_reg_ren;
assign csr_cnn_accel_stat_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == (C_STAT_REG_ADDR >> 2));
logic csr_cnn_accel_stat_reg_ren_ff;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_stat_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_stat_reg_ren_ff <= csr_cnn_accel_stat_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_STAT_REG[0] - TENS_TRANS_SEQ_BUSY - tensor trans. sequence is progressing
// access: ro, hardware: ie
//---------------------
logic  csr_cnn_accel_stat_reg_tens_trans_seq_busy_ff;

assign csr_cnn_accel_stat_reg_rd_data[0] = csr_cnn_accel_stat_reg_tens_trans_seq_busy_ff;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_stat_reg_tens_trans_seq_busy_ff <= 1'b0;
    end else  begin
      if (main_fsm_s_ctrl_if.start & !csr_cnn_accel_stat_reg_tens_trans_seq_busy_ff)
        csr_cnn_accel_stat_reg_tens_trans_seq_busy_ff <= 1'b1;
      else if(main_fsm_s_ctrl_if.done & csr_cnn_accel_stat_reg_tens_trans_seq_busy_ff)
        csr_cnn_accel_stat_reg_tens_trans_seq_busy_ff <= 1'b0;
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_STAT_REG[10:1] - TENS_TRANS_SEQ_CNT - index of the current trans. sequence in progress
// access: ro, hardware: ie
//---------------------
logic [9:0] csr_cnn_accel_stat_reg_tens_trans_seq_cnt_ff; 

assign csr_cnn_accel_stat_reg_rd_data[10:1] = csr_cnn_accel_stat_reg_tens_trans_seq_cnt_ff;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_stat_reg_tens_trans_seq_cnt_ff <= 10'h0;
    end else  begin
        csr_cnn_accel_stat_reg_tens_trans_seq_cnt_ff <= tens_trans_seq_cnt;
    end
end

//------------------------------------------------------------------------------
// CSR:
// [0x8] - CNN_ACCEL_INT_REG - main interrupt register
//------------------------------------------------------------------------------
logic [31:0] csr_cnn_accel_int_reg_rd_data;
assign csr_cnn_accel_int_reg_rd_data[31:9] = 23'h0;

logic csr_cnn_accel_int_reg_ren;
assign csr_cnn_accel_int_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_INT_REG_ADDR >> 2);

logic csr_cnn_accel_int_reg_wen;
assign csr_cnn_accel_int_reg_wen = regmap_reg_wr_en && (regmap_wr_addr == C_INT_REG_ADDR >> 2);

logic csr_cnn_accel_int_reg_ren_ff;
always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_int_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_int_reg_ren_ff <= csr_cnn_accel_int_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_INT_REG[0] - INT_TENS_TRANS_SEQ_DONE_EN - interrupt enable - tensor transformation sequence done
// access: rw, hardware: o
//---------------------
logic  csr_cnn_accel_int_reg_int_tens_trans_seq_done_en_ff;
logic  csr_cnn_accel_int_reg_int_tens_trans_seq_done_clear_ff;


assign csr_cnn_accel_int_reg_rd_data[0] = csr_cnn_accel_int_reg_int_tens_trans_seq_done_en_ff;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_int_reg_int_tens_trans_seq_done_en_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_int_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_int_reg_int_tens_trans_seq_done_en_ff <= regmap_reg_wr_data[0];
            end
        end else begin
            csr_cnn_accel_int_reg_int_tens_trans_seq_done_en_ff <= csr_cnn_accel_int_reg_int_tens_trans_seq_done_en_ff;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_INT_REG[1] - INT_TENS_TRANS_SEQ_DONE_STAT - interrupt status - tensor transformation sequence done
// access: ro, hardware: ie
//---------------------
logic  csr_cnn_accel_int_reg_int_tens_trans_seq_done_stat_ff;

assign csr_cnn_accel_int_reg_rd_data[1] = csr_cnn_accel_int_reg_int_tens_trans_seq_done_stat_ff;


always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_int_reg_int_tens_trans_seq_done_stat_ff <= 1'b0;
    end else  begin
        if (1'b1) begin //TODO: reserved for future implementation
            csr_cnn_accel_int_reg_int_tens_trans_seq_done_stat_ff <= 1'b0; 
        end else if(csr_cnn_accel_int_reg_int_tens_trans_seq_done_clear_ff) begin
            csr_cnn_accel_int_reg_int_tens_trans_seq_done_stat_ff <= 1'b0;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_INT_REG[2] - INT_TENS_TRANS_SEQ_DONE_CLEAR - interrupt clear - tensor transformation sequence done
// access: wosc, hardware: oa
//---------------------

assign csr_cnn_accel_int_reg_rd_data[2] = 1'b0;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_int_reg_int_tens_trans_seq_done_clear_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_int_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_int_reg_int_tens_trans_seq_done_clear_ff <= regmap_reg_wr_data[2];
            end
        end else begin
            csr_cnn_accel_int_reg_int_tens_trans_seq_done_clear_ff <= 1'b0;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_INT_REG[3] - INT_STREAM_H2C_DONE_EN - interrupt enable - tensor transformation sequence done
// access: rw, hardware: o
//---------------------
logic  csr_cnn_accel_int_reg_int_stream_h2c_done_en_ff;
logic  csr_cnn_accel_int_reg_int_stream_h2c_done_clear_ff;

assign csr_cnn_accel_int_reg_rd_data[3] = csr_cnn_accel_int_reg_int_stream_h2c_done_en_ff;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_int_reg_int_stream_h2c_done_en_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_int_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_int_reg_int_stream_h2c_done_en_ff <= regmap_reg_wr_data[3];
            end
        end else begin
            csr_cnn_accel_int_reg_int_stream_h2c_done_en_ff <= csr_cnn_accel_int_reg_int_stream_h2c_done_en_ff;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_INT_REG[4] - INT_STREAM_H2C_DONE_STAT - interrupt status - tensor transformation sequence done
// access: ro, hardware: ie
//---------------------
logic  csr_cnn_accel_int_reg_int_stream_h2c_done_stat_ff;

assign csr_cnn_accel_int_reg_rd_data[4] = csr_cnn_accel_int_reg_int_stream_h2c_done_stat_ff;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_int_reg_int_stream_h2c_done_stat_ff <= 1'b0;
    end else  begin
        if (1'b1) begin
            csr_cnn_accel_int_reg_int_stream_h2c_done_stat_ff <= 1'b0;
        end else if(csr_cnn_accel_int_reg_int_stream_h2c_done_clear_ff) begin
            csr_cnn_accel_int_reg_int_stream_h2c_done_stat_ff <= 1'b0;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_INT_REG[5] - INT_STREAM_H2C_DONE_CLEAR - interrupt clear - tensor transformation sequence done
// access: wosc, hardware: oa
//---------------------

assign csr_cnn_accel_int_reg_rd_data[5] = 1'b0;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_int_reg_int_stream_h2c_done_clear_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_int_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_int_reg_int_stream_h2c_done_clear_ff <= regmap_reg_wr_data[5];
            end
        end else begin
            csr_cnn_accel_int_reg_int_stream_h2c_done_clear_ff <= 1'b0;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_INT_REG[6] - INT_STREAM_C2H_DONE_EN - interrupt enable - tensor transformation sequence done
// access: rw, hardware: o
//---------------------
logic  csr_cnn_accel_int_reg_int_stream_c2h_done_en_ff;
logic  csr_cnn_accel_int_reg_int_stream_c2h_done_clear_ff;

assign csr_cnn_accel_int_reg_rd_data[6] = csr_cnn_accel_int_reg_int_stream_c2h_done_en_ff;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_int_reg_int_stream_c2h_done_en_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_int_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_int_reg_int_stream_c2h_done_en_ff <= regmap_reg_wr_data[6];
            end
        end else begin
            csr_cnn_accel_int_reg_int_stream_c2h_done_en_ff <= csr_cnn_accel_int_reg_int_stream_c2h_done_en_ff;
        end
    end
end

//---------------------
// Bit field:
// CNN_ACCEL_INT_REG[7] - INT_STREAM_C2H_DONE_STAT - interrupt status - tensor transformation sequence done
// access: ro, hardware: ie
//---------------------
logic  csr_cnn_accel_int_reg_int_stream_c2h_done_stat_ff;

assign csr_cnn_accel_int_reg_rd_data[7] = csr_cnn_accel_int_reg_int_stream_c2h_done_stat_ff;


always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_int_reg_int_stream_c2h_done_stat_ff <= 1'b0;
    end else  begin
        if (1'b1) begin
            csr_cnn_accel_int_reg_int_stream_c2h_done_stat_ff <= 1'b0;
        end else if (csr_cnn_accel_int_reg_int_stream_c2h_done_clear_ff) begin
            csr_cnn_accel_int_reg_int_stream_c2h_done_stat_ff <= 1'b0;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_INT_REG[8] - INT_STREAM_C2H_DONE_CLEAR - interrupt clear - tensor transformation sequence done
// access: wosc, hardware: oa
//---------------------

assign csr_cnn_accel_int_reg_rd_data[8] = 1'b0;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_int_reg_int_stream_c2h_done_clear_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_int_reg_wen) begin
            if (regmap_reg_wr_strb[1]) begin
                csr_cnn_accel_int_reg_int_stream_c2h_done_clear_ff <= regmap_reg_wr_data[8];
            end
        end else begin
            csr_cnn_accel_int_reg_int_stream_c2h_done_clear_ff <= 1'b0;
        end
    end
end

//------------------------------------------------------------------------------
// CSR:
// [0x8] - CNN_ACCEL_MMEM_OFFSET_REG - address offset for the main memory access
//------------------------------------------------------------------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_mmem_offset_reg_rd_data;

logic csr_cnn_accel_mmem_offset_reg_wen;
assign csr_cnn_accel_mmem_offset_reg_wen = regmap_reg_wr_en && (regmap_reg_wr_addr == (C_MMEM_OFFSET_REG_ADDR >> 2));

logic csr_cnn_accel_mmem_offset_reg_ren;
assign csr_cnn_accel_mmem_offset_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == (C_MMEM_OFFSET_REG_ADDR >> 2));
logic csr_cnn_accel_mmem_offset_reg_ren_ff;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_mmem_offset_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_mmem_offset_reg_ren_ff <= csr_cnn_accel_mmem_offset_reg_ren;
    end
end

//------------------------------------------------------------------------------
// CSR:
// [0x10] - CNN_ACCEL_GP_RW_REG - general purpose read-write register
//------------------------------------------------------------------------------
logic [31:0] csr_cnn_accel_gp_rw_reg_rd_data;

logic csr_cnn_accel_gp_rw_reg_wen;
assign csr_cnn_accel_gp_rw_reg_wen = regmap_reg_wr_en && (regmap_wr_addr == C_GP_RW_REG_ADDR >> 2);

logic csr_cnn_accel_gp_rw_reg_ren;
assign csr_cnn_accel_gp_rw_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_GP_RW_REG_ADDR >> 2);
logic csr_cnn_accel_gp_rw_reg_ren_ff;
always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_gp_rw_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_gp_rw_reg_ren_ff <= csr_cnn_accel_gp_rw_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_GP_RW_REG[31:0] - GP_RW - general purpose register
// access: rw, hardware: oi
//---------------------
logic [31:0] csr_cnn_accel_gp_rw_reg_gp_rw_ff;

assign csr_cnn_accel_gp_rw_reg_rd_data[31:0] = csr_cnn_accel_gp_rw_reg_gp_rw_ff;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_gp_rw_reg_gp_rw_ff <= 32'h0;
    end else  begin
     if (csr_cnn_accel_gp_rw_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_gp_rw_reg_gp_rw_ff[7:0] <= regmap_reg_wr_data[7:0];
            end
            if (regmap_reg_wr_strb[1]) begin
                csr_cnn_accel_gp_rw_reg_gp_rw_ff[15:8] <= regmap_reg_wr_data[15:8];
            end
            if (regmap_reg_wr_strb[2]) begin
                csr_cnn_accel_gp_rw_reg_gp_rw_ff[23:16] <= regmap_reg_wr_data[23:16];
            end
            if (regmap_reg_wr_strb[3]) begin
                csr_cnn_accel_gp_rw_reg_gp_rw_ff[31:24] <= regmap_reg_wr_data[31:24];
            end
        end else begin            
            csr_cnn_accel_gp_rw_reg_gp_rw_ff <= csr_cnn_accel_gp_rw_reg_gp_rw_ff;
        end
    end
end

//---------------------
// Bit field:
// CNN_ACCEL_MMEM_OFFSET_REG[C_REGMAP_DATA_WDT-1:0] - MMEM_OFFSET - address offset
// access: rw, hardware: ol
//---------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_mmem_offset_reg_mmem_offset_ff;

assign csr_cnn_accel_mmem_offset_reg_rd_data[C_REGMAP_DATA_WDT-1:0] = csr_cnn_accel_mmem_offset_reg_mmem_offset_ff;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_mmem_offset_reg_mmem_offset_ff <= 32'h0;
    end else if (!regmap_ram_lock) begin
     if (csr_cnn_accel_mmem_offset_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_mmem_offset_reg_mmem_offset_ff[7:0] <= regmap_reg_wr_data[7:0];
            end
            if (regmap_reg_wr_strb[1]) begin
                csr_cnn_accel_mmem_offset_reg_mmem_offset_ff[15:8] <= regmap_reg_wr_data[15:8];
            end
            if (regmap_reg_wr_strb[2]) begin
                csr_cnn_accel_mmem_offset_reg_mmem_offset_ff[23:16] <= regmap_reg_wr_data[23:16];
            end
            if (regmap_reg_wr_strb[3]) begin
                csr_cnn_accel_mmem_offset_reg_mmem_offset_ff[C_REGMAP_DATA_WDT-1:24] <= regmap_reg_wr_data[C_REGMAP_DATA_WDT-1:24];
            end
        end else begin
            csr_cnn_accel_mmem_offset_reg_mmem_offset_ff <= csr_cnn_accel_mmem_offset_reg_mmem_offset_ff;
        end
    end
end

//------------------------------------------------------------------------------
// CSR:
// [0xc] - CNN_ACCEL_PERF_RUN_CTRL_REG - performance counter - run cycles - control register
//------------------------------------------------------------------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_perf_run_ctrl_reg_rd_data;
assign csr_cnn_accel_perf_run_ctrl_reg_rd_data[C_REGMAP_DATA_WDT-1:2] = 30'h0;

logic csr_cnn_accel_perf_run_ctrl_reg_wen;
assign csr_cnn_accel_perf_run_ctrl_reg_wen = regmap_reg_wr_en && (regmap_reg_wr_addr == (C_PERF_RUN_CTRL_REG_ADDR >> 2));

logic csr_cnn_accel_perf_run_ctrl_reg_ren;
assign csr_cnn_accel_perf_run_ctrl_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == (C_PERF_RUN_CTRL_REG_ADDR >> 2));
logic csr_cnn_accel_perf_run_ctrl_reg_ren_ff;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_run_ctrl_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_run_ctrl_reg_ren_ff <= csr_cnn_accel_perf_run_ctrl_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_RUN_CTRL_REG[0] - PERF_RUN_EN - perf. counter enable
// access: rw, hardware: o
//---------------------
logic  csr_cnn_accel_perf_run_ctrl_reg_perf_run_en_ff;

assign csr_cnn_accel_perf_run_ctrl_reg_rd_data[0] = csr_cnn_accel_perf_run_ctrl_reg_perf_run_en_ff;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_run_ctrl_reg_perf_run_en_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_perf_run_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_perf_run_ctrl_reg_perf_run_en_ff <= regmap_reg_wr_data[0];
            end
        end else begin
            csr_cnn_accel_perf_run_ctrl_reg_perf_run_en_ff <= csr_cnn_accel_perf_run_ctrl_reg_perf_run_en_ff;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_PERF_RUN_CTRL_REG[1] - PERF_RUN_CLEAR - perf. counter clear
// access: wosc, hardware: oa
//---------------------
logic  csr_cnn_accel_perf_run_ctrl_reg_perf_run_clear_ff;

assign csr_cnn_accel_perf_run_ctrl_reg_rd_data[1] = 1'b0;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_run_ctrl_reg_perf_run_clear_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_perf_run_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_perf_run_ctrl_reg_perf_run_clear_ff <= regmap_reg_wr_data[1];
            end
        end else begin
            csr_cnn_accel_perf_run_ctrl_reg_perf_run_clear_ff <= 1'b0;
        end
    end
end


//------------------------------------------------------------------------------
// CSR:
// [0x10] - CNN_ACCEL_PERF_RUN_LH_REG - performance counter - run cycles - lower half
//------------------------------------------------------------------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_perf_run_lh_reg_rd_data;

logic csr_cnn_accel_perf_run_lh_reg_ren;
assign csr_cnn_accel_perf_run_lh_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == (C_PERF_RUN_LH_REG_ADDR >> 2));
logic csr_cnn_accel_perf_run_lh_reg_ren_ff;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_run_lh_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_run_lh_reg_ren_ff <= csr_cnn_accel_perf_run_lh_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_RUN_LH_REG[C_REGMAP_DATA_WDT-1:0] - PERF_RUN_LH - perf. counter value
// access: ro, hardware: ie
//---------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_perf_run_lh_reg_perf_run_lh_ff;

assign csr_cnn_accel_perf_run_lh_reg_rd_data[C_REGMAP_DATA_WDT-1:0] = csr_cnn_accel_perf_run_lh_reg_perf_run_lh_ff;


always_ff @(posedge clk) begin
    if (!rst_n | csr_cnn_accel_perf_run_ctrl_reg_perf_run_clear_ff) begin
        csr_cnn_accel_perf_run_lh_reg_perf_run_lh_ff <= 32'h0;
    end else  begin
        if(csr_cnn_accel_perf_run_ctrl_reg_perf_run_en_ff & perf_cnt_step_fsm[C_PERF_RUN_OFFSET])
            csr_cnn_accel_perf_run_lh_reg_perf_run_lh_ff <= csr_cnn_accel_perf_run_lh_reg_perf_run_lh_ff + 1;
    end
end


//------------------------------------------------------------------------------
// CSR:
// [0x14] - CNN_ACCEL_PERF_RUN_UH_REG - performance counter - run cycles - upper half
//------------------------------------------------------------------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_perf_run_uh_reg_rd_data;


logic csr_cnn_accel_perf_run_uh_reg_ren;
assign csr_cnn_accel_perf_run_uh_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == (C_PERF_RUN_UH_REG_ADDR >> 2));
logic csr_cnn_accel_perf_run_uh_reg_ren_ff;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_run_uh_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_run_uh_reg_ren_ff <= csr_cnn_accel_perf_run_uh_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_RUN_UH_REG[C_REGMAP_DATA_WDT-1:0] - PERF_RUN_UH - perf. counter value
// access: ro, hardware: ie
//---------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_perf_run_uh_reg_perf_run_uh_ff;

assign csr_cnn_accel_perf_run_uh_reg_rd_data[C_REGMAP_DATA_WDT-1:0] = csr_cnn_accel_perf_run_uh_reg_perf_run_uh_ff;


always_ff @(posedge clk) begin
    if (!rst_n | csr_cnn_accel_perf_run_ctrl_reg_perf_run_clear_ff) begin
        csr_cnn_accel_perf_run_uh_reg_perf_run_uh_ff <= 32'h0;
    end else  begin
        if(csr_cnn_accel_perf_run_ctrl_reg_perf_run_en_ff & perf_cnt_step_fsm[C_PERF_RUN_OFFSET] & csr_cnn_accel_perf_run_lh_reg_perf_run_lh_ff == '1)
            csr_cnn_accel_perf_run_uh_reg_perf_run_uh_ff <= csr_cnn_accel_perf_run_uh_reg_perf_run_uh_ff + 1;
    end
end


//------------------------------------------------------------------------------
// CSR:
// [0x18] - CNN_ACCEL_PERF_COMP_CTRL_REG - performance counter - computation cycles - control register
//------------------------------------------------------------------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_perf_comp_ctrl_reg_rd_data;
assign csr_cnn_accel_perf_comp_ctrl_reg_rd_data[C_REGMAP_DATA_WDT-1:2] = 30'h0;

logic csr_cnn_accel_perf_comp_ctrl_reg_wen;
assign csr_cnn_accel_perf_comp_ctrl_reg_wen = regmap_reg_wr_en && (regmap_reg_wr_addr == (C_PERF_COMP_CTRL_REG_ADDR >> 2));

logic csr_cnn_accel_perf_comp_ctrl_reg_ren;
assign csr_cnn_accel_perf_comp_ctrl_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == (C_PERF_COMP_CTRL_REG_ADDR >> 2));
logic csr_cnn_accel_perf_comp_ctrl_reg_ren_ff;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_comp_ctrl_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_comp_ctrl_reg_ren_ff <= csr_cnn_accel_perf_comp_ctrl_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_COMP_CTRL_REG[0] - PERF_COMP_EN - perf. counter enable
// access: rw, hardware: o
//---------------------
logic  csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_en_ff;

assign csr_cnn_accel_perf_comp_ctrl_reg_rd_data[0] = csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_en_ff;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_en_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_perf_comp_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_en_ff <= regmap_reg_wr_data[0];
            end
        end else begin
            csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_en_ff <= csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_en_ff;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_PERF_COMP_CTRL_REG[1] - PERF_COMP_CLEAR - perf. counter clear
// access: wosc, hardware: oa
//---------------------
logic  csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_clear_ff;

assign csr_cnn_accel_perf_comp_ctrl_reg_rd_data[1] = 1'b0;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_clear_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_perf_comp_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_clear_ff <= regmap_reg_wr_data[1];
            end
        end else begin
            csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_clear_ff <= 1'b0;
        end
    end
end

//------------------------------------------------------------------------------
// CSR:
// [0x1c] - CNN_ACCEL_PERF_COMP_LH_REG - performance counter - run cycles - lower half
//------------------------------------------------------------------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_perf_comp_lh_reg_rd_data;


logic csr_cnn_accel_perf_comp_lh_reg_ren;
assign csr_cnn_accel_perf_comp_lh_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == (C_PERF_COMP_CTRL_REG_ADDR >> 2));
logic csr_cnn_accel_perf_comp_lh_reg_ren_ff;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_comp_lh_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_comp_lh_reg_ren_ff <= csr_cnn_accel_perf_comp_lh_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_COMP_LH_REG[C_REGMAP_DATA_WDT-1:0] - PERF_COMP_LH - perf. counter value
// access: ro, hardware: ie
//---------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_perf_comp_lh_reg_perf_comp_lh_ff;

assign csr_cnn_accel_perf_comp_lh_reg_rd_data[C_REGMAP_DATA_WDT-1:0] = csr_cnn_accel_perf_comp_lh_reg_perf_comp_lh_ff;

always_ff @(posedge clk) begin
    if (!rst_n | csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_clear_ff) begin
        csr_cnn_accel_perf_comp_lh_reg_perf_comp_lh_ff <= 32'h0;
    end else  begin
        if(csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_en_ff & perf_cnt_step_fsm[C_PERF_COMP_OFFSET])
            csr_cnn_accel_perf_comp_lh_reg_perf_comp_lh_ff <= csr_cnn_accel_perf_comp_lh_reg_perf_comp_lh_ff + 1;
    end
end

//------------------------------------------------------------------------------
// CSR:
// [0x20] - CNN_ACCEL_PERF_COMP_UH_REG - performance counter - run cycles - upper half
//------------------------------------------------------------------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_perf_comp_uh_reg_rd_data;


logic csr_cnn_accel_perf_comp_uh_reg_ren;
assign csr_cnn_accel_perf_comp_uh_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == (C_PERF_COMP_UH_REG_ADDR >> 2));
logic csr_cnn_accel_perf_comp_uh_reg_ren_ff;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_comp_uh_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_comp_uh_reg_ren_ff <= csr_cnn_accel_perf_comp_uh_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_COMP_UH_REG[C_REGMAP_DATA_WDT-1:0] - PERF_COMP_UH - perf. counter value
// access: ro, hardware: ie
//---------------------
logic [C_REGMAP_DATA_WDT-1:0] csr_cnn_accel_perf_comp_uh_reg_perf_comp_uh_ff;

assign csr_cnn_accel_perf_comp_uh_reg_rd_data[C_REGMAP_DATA_WDT-1:0] = csr_cnn_accel_perf_comp_uh_reg_perf_comp_uh_ff;

always_ff @(posedge clk) begin
    if (!rst_n | csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_clear_ff) begin
        csr_cnn_accel_perf_comp_uh_reg_perf_comp_uh_ff <= 32'h0;
    end else  begin
        if(csr_cnn_accel_perf_comp_ctrl_reg_perf_comp_en_ff & perf_cnt_step_fsm[C_PERF_COMP_OFFSET] & csr_cnn_accel_perf_comp_lh_reg_perf_comp_lh_ff == '1)
            csr_cnn_accel_perf_comp_uh_reg_perf_comp_uh_ff <= csr_cnn_accel_perf_comp_uh_reg_perf_comp_uh_ff + 1;
    end
end


//------------------------------------------------------------------------------
// CSR:
// [0x2c] - CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG - performance counter - stream H2C cycles - control register
//------------------------------------------------------------------------------
logic [31:0] csr_cnn_accel_perf_stream_c2h_ctrl_reg_rd_data;
assign csr_cnn_accel_perf_stream_c2h_ctrl_reg_rd_data[31:2] = 30'h0;

logic csr_cnn_accel_perf_stream_c2h_ctrl_reg_wen;
assign csr_cnn_accel_perf_stream_c2h_ctrl_reg_wen = regmap_reg_wr_en && (regmap_wr_addr == C_PERF_STREAM_C2H_CTRL_REG_ADDR >> 2);

logic csr_cnn_accel_perf_stream_c2h_ctrl_reg_ren;
assign csr_cnn_accel_perf_stream_c2h_ctrl_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_PERF_STREAM_C2H_CTRL_REG_ADDR >> 2);
logic csr_cnn_accel_perf_stream_c2h_ctrl_reg_ren_ff;
always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_stream_c2h_ctrl_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_stream_c2h_ctrl_reg_ren_ff <= csr_cnn_accel_perf_stream_c2h_ctrl_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG[0] - PERF_STREAM_EN - perf. counter enable
// access: rw, hardware: o
//---------------------
logic  csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_en_ff;

assign csr_cnn_accel_perf_stream_c2h_ctrl_reg_rd_data[0] = csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_en_ff;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_en_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_perf_stream_c2h_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_en_ff <= regmap_reg_wr_data[0];
            end
        end else begin
            csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_en_ff <= csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_en_ff;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG[1] - PERF_STREAM_CLEAR - perf. counter clear
// access: wosc, hardware: oa
//---------------------
logic  csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_clear_ff;

assign csr_cnn_accel_perf_stream_c2h_ctrl_reg_rd_data[1] = 1'b0;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_clear_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_perf_stream_c2h_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_clear_ff <= regmap_reg_wr_data[1];
            end
        end else begin
            csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_clear_ff <= 1'b0;
        end
    end
end


//------------------------------------------------------------------------------
// CSR:
// [0x30] - CNN_ACCEL_PERF_STREAM_C2H_LH_REG - performance counter - run cycles - lower half
//------------------------------------------------------------------------------
logic [31:0] csr_cnn_accel_perf_stream_c2h_lh_reg_rd_data;


logic csr_cnn_accel_perf_stream_c2h_lh_reg_ren;
assign csr_cnn_accel_perf_stream_c2h_lh_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_PERF_STREAM_C2H_LH_REG_ADDR >> 2);
logic csr_cnn_accel_perf_stream_c2h_lh_reg_ren_ff;
always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_stream_c2h_lh_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_stream_c2h_lh_reg_ren_ff <= csr_cnn_accel_perf_stream_c2h_lh_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_STREAM_C2H_LH_REG[31:0] - PERF_STREAM_LH - perf. counter value
// access: ro, hardware: ie
//---------------------
logic [31:0] csr_cnn_accel_perf_stream_c2h_lh_reg_perf_stream_lh_ff;

assign csr_cnn_accel_perf_stream_c2h_lh_reg_rd_data[31:0] = csr_cnn_accel_perf_stream_c2h_lh_reg_perf_stream_lh_ff;


always @(posedge clk) begin
    if (!rst_n | csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_clear_ff) begin
        csr_cnn_accel_perf_stream_c2h_lh_reg_perf_stream_lh_ff <= 32'h0;
    end else  begin
        if (csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_en_ff & perf_cnt_step_fsm[C_PERF_STREAM_C2H_OFFSET]) begin
            csr_cnn_accel_perf_stream_c2h_lh_reg_perf_stream_lh_ff <= csr_cnn_accel_perf_stream_c2h_lh_reg_perf_stream_lh_ff + 1;
        end
    end
end


//------------------------------------------------------------------------------
// CSR:
// [0x34] - CNN_ACCEL_PERF_STREAM_C2H_UH_REG - performance counter - run cycles - upper half
//------------------------------------------------------------------------------
logic [31:0] csr_cnn_accel_perf_stream_c2h_uh_reg_rd_data;


logic csr_cnn_accel_perf_stream_c2h_uh_reg_ren;
assign csr_cnn_accel_perf_stream_c2h_uh_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_PERF_STREAM_C2H_UH_REG_ADDR >> 2);
logic csr_cnn_accel_perf_stream_c2h_uh_reg_ren_ff;
always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_stream_c2h_uh_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_stream_c2h_uh_reg_ren_ff <= csr_cnn_accel_perf_stream_c2h_uh_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_STREAM_C2H_UH_REG[31:0] - PERF_STREAM_UH - perf. counter value
// access: ro, hardware: ie
//---------------------
logic [31:0] csr_cnn_accel_perf_stream_c2h_uh_reg_perf_stream_uh_ff;

assign csr_cnn_accel_perf_stream_c2h_uh_reg_rd_data[31:0] = csr_cnn_accel_perf_stream_c2h_uh_reg_perf_stream_uh_ff;


always @(posedge clk) begin
    if (!rst_n | csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_clear_ff) begin
        csr_cnn_accel_perf_stream_c2h_uh_reg_perf_stream_uh_ff <= 32'h0;
    end else  begin
      if (csr_cnn_accel_perf_stream_c2h_ctrl_reg_perf_stream_en_ff & perf_cnt_step_fsm[C_PERF_STREAM_C2H_OFFSET] & csr_cnn_accel_perf_stream_c2h_lh_reg_perf_stream_lh_ff == '1) begin
            csr_cnn_accel_perf_stream_c2h_uh_reg_perf_stream_uh_ff <= csr_cnn_accel_perf_stream_c2h_uh_reg_perf_stream_uh_ff + 1;
        end
    end
end

//------------------------------------------------------------------------------
// CSR:
// [0x2c] - CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG - performance counter - stream H2C cycles - control register
//------------------------------------------------------------------------------
logic [31:0] csr_cnn_accel_perf_stream_h2c_ctrl_reg_rd_data;
assign csr_cnn_accel_perf_stream_h2c_ctrl_reg_rd_data[31:2] = 30'h0;

logic csr_cnn_accel_perf_stream_h2c_ctrl_reg_wen;
assign csr_cnn_accel_perf_stream_h2c_ctrl_reg_wen = regmap_reg_wr_en && (regmap_wr_addr == C_PERF_STREAM_H2C_CTRL_REG_ADDR >> 2);

logic csr_cnn_accel_perf_stream_h2c_ctrl_reg_ren;
assign csr_cnn_accel_perf_stream_h2c_ctrl_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_PERF_STREAM_H2C_CTRL_REG_ADDR >> 2);
logic csr_cnn_accel_perf_stream_h2c_ctrl_reg_ren_ff;
always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_stream_h2c_ctrl_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_stream_h2c_ctrl_reg_ren_ff <= csr_cnn_accel_perf_stream_h2c_ctrl_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG[0] - PERF_STREAM_EN - perf. counter enable
// access: rw, hardware: o
//---------------------
logic  csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_en_ff;

assign csr_cnn_accel_perf_stream_h2c_ctrl_reg_rd_data[0] = csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_en_ff;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_en_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_perf_stream_h2c_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_en_ff <= regmap_reg_wr_data[0];
            end
        end else begin
            csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_en_ff <= csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_en_ff;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG[1] - PERF_STREAM_CLEAR - perf. counter clear
// access: wosc, hardware: oa
//---------------------
logic  csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_clear_ff;

assign csr_cnn_accel_perf_stream_h2c_ctrl_reg_rd_data[1] = 1'b0;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_clear_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_perf_stream_h2c_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_clear_ff <= regmap_reg_wr_data[1];
            end
        end else begin
            csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_clear_ff <= 1'b0;
        end
    end
end


//------------------------------------------------------------------------------
// CSR:
// [0x30] - CNN_ACCEL_PERF_STREAM_H2C_LH_REG - performance counter - run cycles - lower half
//------------------------------------------------------------------------------
logic [31:0] csr_cnn_accel_perf_stream_h2c_lh_reg_rd_data;


logic csr_cnn_accel_perf_stream_h2c_lh_reg_ren;
assign csr_cnn_accel_perf_stream_h2c_lh_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_PERF_STREAM_H2C_LH_REG_ADDR >> 2);
logic csr_cnn_accel_perf_stream_h2c_lh_reg_ren_ff;
always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_stream_h2c_lh_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_stream_h2c_lh_reg_ren_ff <= csr_cnn_accel_perf_stream_h2c_lh_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_STREAM_H2C_LH_REG[31:0] - PERF_STREAM_LH - perf. counter value
// access: ro, hardware: ie
//---------------------
logic [31:0] csr_cnn_accel_perf_stream_h2c_lh_reg_perf_stream_lh_ff;

assign csr_cnn_accel_perf_stream_h2c_lh_reg_rd_data[31:0] = csr_cnn_accel_perf_stream_h2c_lh_reg_perf_stream_lh_ff;


always @(posedge clk) begin
    if (!rst_n | csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_clear_ff) begin
        csr_cnn_accel_perf_stream_h2c_lh_reg_perf_stream_lh_ff <= 32'h0;
    end else  begin
        if (csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_en_ff & perf_cnt_step_fsm[C_PERF_STREAM_H2C_OFFSET]) begin
            csr_cnn_accel_perf_stream_h2c_lh_reg_perf_stream_lh_ff <= csr_cnn_accel_perf_stream_h2c_lh_reg_perf_stream_lh_ff + 1;
        end
    end
end


//------------------------------------------------------------------------------
// CSR:
// [0x34] - CNN_ACCEL_PERF_STREAM_H2C_UH_REG - performance counter - run cycles - upper half
//------------------------------------------------------------------------------
logic [31:0] csr_cnn_accel_perf_stream_h2c_uh_reg_rd_data;


logic csr_cnn_accel_perf_stream_h2c_uh_reg_ren;
assign csr_cnn_accel_perf_stream_h2c_uh_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_PERF_STREAM_H2C_UH_REG_ADDR >> 2);
logic csr_cnn_accel_perf_stream_h2c_uh_reg_ren_ff;
always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_stream_h2c_uh_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_stream_h2c_uh_reg_ren_ff <= csr_cnn_accel_perf_stream_h2c_uh_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_STREAM_H2C_UH_REG[31:0] - PERF_STREAM_UH - perf. counter value
// access: ro, hardware: ie
//---------------------
logic [31:0] csr_cnn_accel_perf_stream_h2c_uh_reg_perf_stream_uh_ff;

assign csr_cnn_accel_perf_stream_h2c_uh_reg_rd_data[31:0] = csr_cnn_accel_perf_stream_h2c_uh_reg_perf_stream_uh_ff;


always @(posedge clk) begin
    if (!rst_n | csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_clear_ff) begin
        csr_cnn_accel_perf_stream_h2c_uh_reg_perf_stream_uh_ff <= 32'h0;
    end else  begin
      if (csr_cnn_accel_perf_stream_h2c_ctrl_reg_perf_stream_en_ff & perf_cnt_step_fsm[C_PERF_STREAM_H2C_OFFSET] & csr_cnn_accel_perf_stream_h2c_lh_reg_perf_stream_lh_ff == '1) begin
            csr_cnn_accel_perf_stream_h2c_uh_reg_perf_stream_uh_ff <= csr_cnn_accel_perf_stream_h2c_uh_reg_perf_stream_uh_ff + 1;
        end
    end
end

//------------------------------------------------------------------------------
// CSR:
// [0x44] - CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG - performance counter - stream H2C cycles - control register
//------------------------------------------------------------------------------
logic [31:0] csr_cnn_accel_perf_cache_stall_ctrl_reg_rd_data;
assign csr_cnn_accel_perf_cache_stall_ctrl_reg_rd_data[31:2] = 30'h0;

logic csr_cnn_accel_perf_cache_stall_ctrl_reg_wen;
assign csr_cnn_accel_perf_cache_stall_ctrl_reg_wen = regmap_reg_wr_en && (regmap_wr_addr == C_PERF_CACHE_STALL_CTRL_REG_ADDR >> 2);

logic csr_cnn_accel_perf_cache_stall_ctrl_reg_ren;
assign csr_cnn_accel_perf_cache_stall_ctrl_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_PERF_CACHE_STALL_CTRL_REG_ADDR >> 2);
logic csr_cnn_accel_perf_cache_stall_ctrl_reg_ren_ff;
always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_cache_stall_ctrl_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_cache_stall_ctrl_reg_ren_ff <= csr_cnn_accel_perf_cache_stall_ctrl_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG[0] - PERF_STREAM_EN - perf. counter enable
// access: rw, hardware: o
//---------------------
logic  csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_en_ff;

assign csr_cnn_accel_perf_cache_stall_ctrl_reg_rd_data[0] = csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_en_ff;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_en_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_perf_cache_stall_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_en_ff <= regmap_reg_wr_data[0];
            end
        end else begin
            csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_en_ff <= csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_en_ff;
        end
    end
end


//---------------------
// Bit field:
// CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG[1] - PERF_STREAM_CLEAR - perf. counter clear
// access: wosc, hardware: oa
//---------------------
logic  csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_clear_ff;

assign csr_cnn_accel_perf_cache_stall_ctrl_reg_rd_data[1] = 1'b0;

always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_clear_ff <= 1'b0;
    end else  begin
     if (csr_cnn_accel_perf_cache_stall_ctrl_reg_wen) begin
            if (regmap_reg_wr_strb[0]) begin
                csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_clear_ff <= regmap_reg_wr_data[1];
            end
        end else begin
            csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_clear_ff <= 1'b0;
        end
    end
end


//------------------------------------------------------------------------------
// CSR:
// [0x30] - CNN_ACCEL_PERF_CACHE_STALL_LH_REG - performance counter - run cycles - lower half
//------------------------------------------------------------------------------
logic [31:0] csr_cnn_accel_perf_cache_stall_lh_reg_rd_data;


logic csr_cnn_accel_perf_cache_stall_lh_reg_ren;
assign csr_cnn_accel_perf_cache_stall_lh_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_PERF_CACHE_STALL_LH_REG_ADDR >> 2);
logic csr_cnn_accel_perf_cache_stall_lh_reg_ren_ff;
always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_cache_stall_lh_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_cache_stall_lh_reg_ren_ff <= csr_cnn_accel_perf_cache_stall_lh_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_CACHE_STALL_LH_REG[31:0] - PERF_STREAM_LH - perf. counter value
// access: ro, hardware: ie
//---------------------
logic [31:0] csr_cnn_accel_perf_cache_stall_lh_reg_perf_stream_lh_ff;

assign csr_cnn_accel_perf_cache_stall_lh_reg_rd_data[31:0] = csr_cnn_accel_perf_cache_stall_lh_reg_perf_stream_lh_ff;


always @(posedge clk) begin
    if (!rst_n | csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_clear_ff) begin
        csr_cnn_accel_perf_cache_stall_lh_reg_perf_stream_lh_ff <= 32'h0;
    end else  begin
        if (csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_en_ff & perf_cnt_step_fsm[C_PERF_CACHE_STALL_OFFSET]) begin
            csr_cnn_accel_perf_cache_stall_lh_reg_perf_stream_lh_ff <= csr_cnn_accel_perf_cache_stall_lh_reg_perf_stream_lh_ff + 1;
        end
    end
end


//------------------------------------------------------------------------------
// CSR:
// [0x34] - CNN_ACCEL_PERF_CACHE_STALL_UH_REG - performance counter - run cycles - upper half
//------------------------------------------------------------------------------
logic [31:0] csr_cnn_accel_perf_cache_stall_uh_reg_rd_data;


logic csr_cnn_accel_perf_cache_stall_uh_reg_ren;
assign csr_cnn_accel_perf_cache_stall_uh_reg_ren = regmap_reg_rd_en && (regmap_reg_rd_addr == C_PERF_CACHE_STALL_UH_REG_ADDR >> 2);
logic csr_cnn_accel_perf_cache_stall_uh_reg_ren_ff;
always @(posedge clk) begin
    if (!rst_n) begin
        csr_cnn_accel_perf_cache_stall_uh_reg_ren_ff <= 1'b0;
    end else begin
        csr_cnn_accel_perf_cache_stall_uh_reg_ren_ff <= csr_cnn_accel_perf_cache_stall_uh_reg_ren;
    end
end
//---------------------
// Bit field:
// CNN_ACCEL_PERF_CACHE_STALL_UH_REG[31:0] - PERF_STREAM_UH - perf. counter value
// access: ro, hardware: ie
//---------------------
logic [31:0] csr_cnn_accel_perf_cache_stall_uh_reg_perf_stream_uh_ff;

assign csr_cnn_accel_perf_cache_stall_uh_reg_rd_data[31:0] = csr_cnn_accel_perf_cache_stall_uh_reg_perf_stream_uh_ff;


always @(posedge clk) begin
    if (!rst_n | csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_clear_ff) begin
        csr_cnn_accel_perf_cache_stall_uh_reg_perf_stream_uh_ff <= 32'h0;
    end else  begin
      if (csr_cnn_accel_perf_cache_stall_ctrl_reg_perf_stream_en_ff & perf_cnt_step_fsm[C_PERF_CACHE_STALL_OFFSET] & csr_cnn_accel_perf_cache_stall_lh_reg_perf_stream_lh_ff == '1) begin
            csr_cnn_accel_perf_cache_stall_uh_reg_perf_stream_uh_ff <= csr_cnn_accel_perf_cache_stall_uh_reg_perf_stream_uh_ff + 1;
        end
    end
end

always_ff @(posedge clk) begin
    if (!rst_n) begin
        regmap_reg_rd_data <= 32'h0;
    end else if (regmap_reg_rd_en) begin
        case (regmap_reg_rd_addr)
            (C_CTRL_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_ctrl_reg_rd_data;
            (C_STAT_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_stat_reg_rd_data;
            (C_INT_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_int_reg_rd_data; 
            (C_MMEM_OFFSET_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_mmem_offset_reg_rd_data;
            (C_GP_RW_REG_ADDR >> 2): regmap_reg_rd_data <=csr_cnn_accel_gp_rw_reg_rd_data;
            (C_PERF_RUN_CTRL_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_run_ctrl_reg_rd_data;
            (C_PERF_RUN_LH_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_run_lh_reg_rd_data;
            (C_PERF_RUN_UH_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_run_uh_reg_rd_data;
            (C_PERF_COMP_CTRL_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_comp_ctrl_reg_rd_data;
            (C_PERF_COMP_LH_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_comp_lh_reg_rd_data;
            (C_PERF_COMP_UH_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_comp_uh_reg_rd_data;
            (C_PERF_STREAM_C2H_CTRL_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_stream_c2h_ctrl_reg_rd_data;
            (C_PERF_STREAM_C2H_LH_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_stream_c2h_lh_reg_rd_data;
            (C_PERF_STREAM_C2H_UH_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_stream_c2h_uh_reg_rd_data;
            (C_PERF_STREAM_H2C_CTRL_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_stream_h2c_ctrl_reg_rd_data;
            (C_PERF_STREAM_H2C_LH_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_stream_h2c_lh_reg_rd_data;
            (C_PERF_STREAM_H2C_UH_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_stream_h2c_uh_reg_rd_data;
            (C_PERF_CACHE_STALL_CTRL_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_cache_stall_ctrl_reg_rd_data;
            (C_PERF_CACHE_STALL_LH_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_cache_stall_lh_reg_rd_data;
            (C_PERF_CACHE_STALL_UH_REG_ADDR >> 2): regmap_reg_rd_data <= csr_cnn_accel_perf_cache_stall_uh_reg_rd_data;
            default: regmap_reg_rd_data <= 32'h0;
        endcase
    end else begin
        regmap_reg_rd_data <= 32'h0;
    end
end

always_ff @(posedge clk) begin : main_fsm_start_reg
    if (!rst_n) begin
        main_fsm_s_ctrl_if.start <= 1'b0;
    end else  begin
        main_fsm_s_ctrl_if.start <= csr_cnn_accel_ctrl_reg_tens_trans_seq_start_ff;
    end
end

always_ff @(posedge clk) begin : tens_trans_seq_lim_reg
    if (!rst_n) begin
        tens_trans_seq_lim <= '0;
    end else  begin
        tens_trans_seq_lim <= csr_cnn_accel_ctrl_reg_tens_trans_seq_len_ff;
    end
end

always_ff @(posedge clk) begin : soft_rst_reg
    if (!rst_n) begin
        soft_rst <= '0;
    end else  begin
        soft_rst <= csr_cnn_accel_ctrl_reg_soft_reset_ff;
    end
end

//RAM memory region will be locked when tens. trans. is in progress
assign regmap_ram_lock = csr_cnn_accel_stat_reg_tens_trans_seq_busy_ff;

//synthesis translate_off

//internal and external interfaces never collide
always_ff @(posedge clk) assert (!(main_fsm_regmap_rd_if.rd_en & s_axil_regmap_rd_if.rd_en) | !rst_n)  else $error("Read collision in regmap shall not occur!");

//synthesis translate_on

endmodule