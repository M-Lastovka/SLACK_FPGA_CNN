`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     add_cell
// Project Name:    Efficient FPGA CNN implementation
// Description:     addition primitive, non-blocking, both operands and result 
//                  shall be of same arithmetic configuration
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;

module add_cell
#(
    parameter arith_cfg_t ADD_ARITH_CFG = '{word_wdt:16, fxp_cfg:'{int_wdt:8, frac_wdt:8}, arith_type:FIXED_POINT_GENERIC, arith_satur:1},
    parameter ADD_IN_CYC_LEN = 1,
    parameter ADD_OUT_CYC_LEN = 1
)
(
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    input  logic [ADD_ARITH_CFG.word_wdt-1:0] add_op_a,
    input  logic [ADD_ARITH_CFG.word_wdt-1:0] add_op_b,
    input  logic add_op_val,
    output logic [ADD_ARITH_CFG.word_wdt-1:0] add_res,
    output logic add_res_val
);

generate 
    if(ADD_ARITH_CFG.arith_type == FIXED_POINT_GENERIC) begin : fxp_add
 
        logic [ADD_ARITH_CFG.word_wdt-1:0] add_res_init;
        logic [ADD_ARITH_CFG.word_wdt-1:0] add_res_q;
        logic [ADD_ARITH_CFG.word_wdt-1:0] add_res_init_del;
        logic [2*ADD_ARITH_CFG.word_wdt-1:0] add_op_in_del;
        logic [ADD_ARITH_CFG.word_wdt-1:0] add_op_a_del;
        logic [ADD_ARITH_CFG.word_wdt-1:0] add_op_b_del;
        logic add_op_val_in_del;
        logic overflow_flag;

        del_chain //input registering
        #(
            .IN_WORD_WDT(2*ADD_ARITH_CFG.word_wdt),
            .DEL_CYC_LEN(ADD_IN_CYC_LEN)
        )
        in_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word({add_op_a, add_op_b}),
            .in_word_val(add_op_val),
            .in_word_del(add_op_in_del),
            .in_word_val_del(add_op_val_in_del)
        );

        always_comb  begin : add_proc
            add_op_a_del = add_op_in_del[2*ADD_ARITH_CFG.word_wdt-1-:ADD_ARITH_CFG.word_wdt];
            add_op_b_del = add_op_in_del[0+:ADD_ARITH_CFG.word_wdt];
            add_res_init = $signed(add_op_a_del) + $signed(add_op_b_del);

            //generate overflow bit
            overflow_flag = add_op_a_del[ADD_ARITH_CFG.word_wdt-1] == add_op_b_del[ADD_ARITH_CFG.word_wdt-1] & add_op_a_del[ADD_ARITH_CFG.word_wdt-1] != add_res_init[ADD_ARITH_CFG.word_wdt-1];

            //normalize word to fit into original word length, perform saturation & rounding
            if(ADD_ARITH_CFG.arith_satur)
                if(overflow_flag)
                    add_res_q = {!add_res_init[ADD_ARITH_CFG.word_wdt-1], {(ADD_ARITH_CFG.word_wdt-1){add_res_init[ADD_ARITH_CFG.word_wdt-1]}}}; //saturation
                else
                    add_res_q = add_res_init; 
            else
                add_res_q = add_res_init; 
        end

        del_chain //output registering
        #(
            .IN_WORD_WDT(ADD_ARITH_CFG.word_wdt),
            .DEL_CYC_LEN(ADD_OUT_CYC_LEN)
        )
        out_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word(add_res_q),
            .in_word_val(add_op_val_in_del),
            .in_word_del(add_res),
            .in_word_val_del(add_res_val)
        );
    end else if(ADD_ARITH_CFG.arith_type == ADDR_OPT_FPGA) begin

        logic [ADD_ARITH_CFG.word_wdt:0] add_res_i;

        dsp_macro_addr_add_32_bit addr_add 
        (
          .CLK(clk),      
          .CE(clk_en),        
          .SCLR(!rst_n),    
          .C(add_op_a),          
          .CONCAT(add_op_b),
          .P(add_res_i)           
        );

        assign add_res = add_res_i[ADD_ARITH_CFG.word_wdt-1:0];

        del_chain //valid registering
        #(
            .IN_WORD_WDT(1),
            .DEL_CYC_LEN(2)
        )
        out_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word(add_op_val),
            .in_word_val(),
            .in_word_del(add_res_val),
            .in_word_val_del()
        );
    end
endgenerate

endmodule