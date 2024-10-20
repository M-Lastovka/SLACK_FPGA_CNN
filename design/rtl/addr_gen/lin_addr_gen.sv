`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     lin_addr_gen
// Project Name:    Efficient FPGA CNN implementation
// Description:     compute the linear index (vector address) based on 2D indices
//                  address is computed thusly: addr = col_i + mult_const*row_i + offset (in column-first case, otherwise col_i and row_i are switched)
//                  the mult_const is determined by matrix row or col dim, the offset by tensor address and data type
//                  the computation is pipelined, first (offset + col_i) and (mult_const*row_i) are computed in parallel, then added
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;
import mem_pckg::*;

module lin_addr_gen
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    input  tens_trans_spec_t  lin_tens_trans_spec,
    //data & address 
    input  mem_cmd_rd_t addr_gen_rd_mmem_i,
    input  logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_mult_op_a,
    input  logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_mult_op_b,
    input  logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_add_op_a,
    input  logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_add_op_b,
    output mem_cmd_rd_t addr_gen_lin_rd_mmem_q
);

mem_cmd_rd_t addr_gen_rd_mmem_ii;   
mem_cmd_rd_t addr_gen_lin_rd_mmem_fin;
mem_cmd_rd_t addr_gen_lin_rd_mmem_fin_del;
logic addr_gen_rd_addr_val;
logic addr_gen_rd_mult_res_val;
logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_add_res; 
logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_add_res_i;
logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_mult_res; 
logic [C_MMEM_ADDR_WDT-1:0] addr_gen_rd_addr;


del_chain //delay the read command data while the address is being computed
#(
    .IN_WORD_WDT($bits(addr_gen_rd_mmem_i)),
    .DEL_CYC_LEN(C_ADDR_GEN_RD_COMP_CYC_LEN)
)
addr_gen_mmem_rd_cmd_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(addr_gen_rd_mmem_i),
    .in_word_val(),
    .in_word_del(addr_gen_rd_mmem_ii),
    .in_word_val_del()
);

mult_cell //multiplier
#(
    .MULT_ARITH_CFG(C_ADDR_MULT_ARITH_CFG),
    .MULT_IN_CYC_LEN(C_MULT_ADDR_IN_CYC_LEN),
    .MULT_OUT_CYC_LEN(C_MULT_ADDR_OUT_CYC_LEN)
)
addr_gen_rd_mult
( 
  .clk(clk),
  .rst_n(rst_n),
  .clk_en(clk_en),
  .mult_op_a(addr_gen_rd_mult_op_a), 
  .mult_op_b(addr_gen_rd_mult_op_b),
  .mult_op_val(addr_gen_rd_mmem_i.cmd_rd_en),
  .mult_res(addr_gen_rd_mult_res),
  .mult_res_val(addr_gen_rd_mult_res_val)
);

add_cell //adder
#(
    .ADD_ARITH_CFG(C_ADDR_ADD_ARITH_CFG),
    .ADD_IN_CYC_LEN(C_ADD_ADDR_IN_CYC_LEN),
    .ADD_OUT_CYC_LEN(C_ADD_ADDR_OUT_CYC_LEN)
)
addr_gen_rd_add
( 
  .clk(clk),
  .rst_n(rst_n),
  .clk_en(clk_en),
  .add_op_a(addr_gen_rd_add_op_a), 
  .add_op_b(addr_gen_rd_add_op_b),
  .add_op_val(addr_gen_rd_mmem_i.cmd_rd_en),
  .add_res(addr_gen_rd_add_res),
  .add_res_val()
);

del_chain //delay the adder result to match multiplier latency
#(
    .IN_WORD_WDT(C_MMEM_ADDR_WDT),
    .DEL_CYC_LEN(C_MULT_ADDR_CYC_LEN - C_ADD_ADDR_CYC_LEN)
)
addr_gen_rd_add_res_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(addr_gen_rd_add_res),
    .in_word_val(),
    .in_word_del(addr_gen_rd_add_res_i),
    .in_word_val_del()
);

add_cell //final adder
#(
    .ADD_ARITH_CFG(C_ADDR_ADD_ARITH_CFG),
    .ADD_IN_CYC_LEN(C_ADD_ADDR_IN_CYC_LEN),
    .ADD_OUT_CYC_LEN(C_ADD_ADDR_OUT_CYC_LEN)
)
addr_gen_rd_fin_add
( 
  .clk(clk),
  .rst_n(rst_n),
  .clk_en(clk_en),
  .add_op_a(addr_gen_rd_add_res_i), 
  .add_op_b(addr_gen_rd_mult_res),
  .add_op_val(addr_gen_rd_mult_res_val),
  .add_res(addr_gen_rd_addr),
  .add_res_val(addr_gen_rd_addr_val)
);

always_comb begin //assign the computed address
    addr_gen_lin_rd_mmem_fin = addr_gen_rd_mmem_ii;
    addr_gen_lin_rd_mmem_fin.cmd_rd_addr = addr_gen_rd_addr_val ? addr_gen_rd_addr : '0;
end

del_chain //delay final address in case of convolution
#(
    .IN_WORD_WDT($bits(addr_gen_rd_mmem_i)),
    .DEL_CYC_LEN(C_CONV_ADDR_GEN_LIN_DEL_CYC_LEN)
)
addr_gen_rd_fin_cmd_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(addr_gen_lin_rd_mmem_fin),
    .in_word_val(),
    .in_word_del(addr_gen_lin_rd_mmem_fin_del),
    .in_word_val_del()
);

always_comb begin //final mux - choose the delayed version if the data is part of convolution
    if(lin_tens_trans_spec.tens_trans_cfg.tens_trans_type == TRANS_CONV) begin
        addr_gen_lin_rd_mmem_q = addr_gen_lin_rd_mmem_fin_del;
    end else begin
        addr_gen_lin_rd_mmem_q = addr_gen_lin_rd_mmem_fin;
    end
end

// synthesis translate_off

//assertions
// synthesis translate_on

endmodule