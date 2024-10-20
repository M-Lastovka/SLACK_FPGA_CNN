`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     add_tree
// Project Name:    Efficient FPGA CNN implementation
// Description:     An adder tree utilizing the adder cell, recursive instantiation,
//                  requires power of 2 operands
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module add_tree
#(
    parameter IN_VLW_WDT
) 
(
    input logic  clk,
    input logic  rst_n,
    input logic  clk_en,
    input logic  [IN_VLW_WDT-1:0]            in_vlw,
    output logic [C_ADD_ARITH_CFG.word_wdt-1:0]  out_vlw
);
  
logic [C_ADD_ARITH_CFG.word_wdt-1:0]  res_add;
logic [C_ADD_ARITH_CFG.word_wdt-1:0]  res_add_q;
logic [IN_VLW_WDT/2-1:0] op_a;
logic [IN_VLW_WDT/2-1:0] op_b;

generate
  if(IN_VLW_WDT == C_ADD_ARITH_CFG.word_wdt) begin : no_adder //no merging adder needed
      assign out_vlw = in_vlw;
  end
  else if (IN_VLW_WDT == C_ADD_ARITH_CFG.word_wdt*2) begin : leaf
      assign op_a = in_vlw[IN_VLW_WDT-1 -: IN_VLW_WDT/2];
      assign op_b = in_vlw[IN_VLW_WDT/2-1 -: IN_VLW_WDT/2];
  end else begin : node   
      //left tree
      add_tree 
      #(
          .IN_VLW_WDT(IN_VLW_WDT/2)
      ) 
      left_tree
      (
          .clk(clk),
          .rst_n(rst_n),
          .clk_en(clk_en),
          .in_vlw(in_vlw[IN_VLW_WDT-1 -: IN_VLW_WDT/2]),
          .out_vlw(op_a)
      );
     
      //right tree
      add_tree
      #(
          .IN_VLW_WDT (IN_VLW_WDT/2)
      ) 
      right_tree
      (
          .clk(clk),
          .rst_n(rst_n),
          .clk_en(clk_en),
          .in_vlw(in_vlw[IN_VLW_WDT/2-1 -: IN_VLW_WDT/2]),
          .out_vlw(op_b)
      );

  end
endgenerate

generate
  if(IN_VLW_WDT != C_ADD_ARITH_CFG.word_wdt) begin
    add_cell
    #(
    .ADD_ARITH_CFG(C_ADD_ARITH_CFG),
    .ADD_IN_CYC_LEN(C_ADD_FXP_IN_CYC_LEN),
    .ADD_OUT_CYC_LEN(C_ADD_FXP_OUT_CYC_LEN)
    )
    add_tree_node_inst
    ( 
      .clk(clk),
      .rst_n(rst_n),
      .clk_en(clk_en),
      .add_op_a(op_a), 
      .add_op_b(op_b),
      .add_op_val(),
      .add_res(res_add_q),
      .add_res_val()
    );

    del_chain //delay chain before the results enter the next stage
    #(
        .IN_WORD_WDT(C_PIPE_DATA_WDT),
        .DEL_CYC_LEN(C_ADD_TREE_LVL_DEL_CYC_LEN)
    )
    add_tree_lvl_del_chain
    (
        .clk(clk),
        .rst_n(rst_n),
        .clk_en(clk_en),
        .in_word(res_add_q),
        .in_word_val(),
        .in_word_del(out_vlw), 
        .in_word_val_del()
    );
  end
endgenerate

endmodule