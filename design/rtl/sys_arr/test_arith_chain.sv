`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 04/19/2024 10:43:29 PM
// Design Name: 
// Module Name: dig
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;

module test_arith_chain
#(
    parameter LEN = 256
) 
(
    //clk&reset
    input clk,
    input rst_n,
    input clk_en,
    //data
    input  logic [C_ARITH_WORD_LEN-1:0] op_a, op_b,
    output logic [C_ARITH_WORD_LEN-1:0] res_mult,
    output logic [C_ARITH_WORD_LEN-1:0] res_add
    );
    
    logic [C_ARITH_WORD_LEN-1:0] in_arr_a[LEN+1];
    logic [C_ARITH_WORD_LEN-1:0] in_arr_b[LEN+1];
    
    assign in_arr_a[0] = op_a;
    assign in_arr_b[0] = op_b;
    assign res_mult = in_arr_a[LEN];
    assign res_add  = in_arr_b[LEN];
    
    genvar i;
	generate
	  for (i = 0; i < LEN; i++) begin
        add_cell
        #(
        .ADD_ARITH_CFG(C_ADD_ARITH_CFG),
        .ADD_IN_CYC_LEN(C_ADD_FXP_IN_CYC_LEN),
        .ADD_OUT_CYC_LEN(C_ADD_FXP_OUT_CYC_LEN)
        )
        add_inst
        ( 
          .clk(clk),
          .rst_n(rst_n),
          .clk_en(clk_en),
          .add_op_a(in_arr_a[i]), 
          .add_op_b(in_arr_b[i]),
          .add_op_val(1),
          .add_res(in_arr_b[i+1]),
          .add_res_val()
        );
        
        mult_cell
        #(
        .MULT_ARITH_CFG(C_MULT_ARITH_CFG),
        .MULT_IN_CYC_LEN(C_MULT_FXP_IN_CYC_LEN),
        .MULT_OUT_CYC_LEN(C_MULT_FXP_OUT_CYC_LEN)
        )
        mult_inst
        ( 
          .clk(clk),
          .rst_n(rst_n),
          .clk_en(clk_en),
          .mult_op_a(in_arr_a[i]), 
          .mult_op_b(in_arr_b[i]),
          .mult_op_val(1),
          .mult_res(in_arr_a[i+1]),
          .mult_res_val()
        );
	  end
	endgenerate
endmodule
