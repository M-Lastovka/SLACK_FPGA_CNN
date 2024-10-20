`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     mult_cell
// Project Name:    Efficient FPGA CNN implementation
// Description:     multiplication primitive, non-blocking, both operands and result 
//                  shall be of same arithmetic configuration
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;

module mult_cell
#(
    parameter arith_cfg_t MULT_ARITH_CFG = '{word_wdt:16, fxp_cfg:'{int_wdt:8, frac_wdt:8}, arith_type:FIXED_POINT_GENERIC, arith_satur:1},
    parameter MULT_IN_CYC_LEN = 1,
    parameter MULT_OUT_CYC_LEN = 1
)
(
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    input  logic [MULT_ARITH_CFG.word_wdt-1:0] mult_op_a,
    input  logic [MULT_ARITH_CFG.word_wdt-1:0] mult_op_b,
    input  logic mult_op_val,
    output logic [MULT_ARITH_CFG.word_wdt-1:0] mult_res,
    output logic mult_res_val
);

localparam MULT_CYC_LEN = MULT_IN_CYC_LEN + MULT_OUT_CYC_LEN;

generate 
    if(MULT_ARITH_CFG.arith_type == FIXED_POINT_GENERIC) begin : fxp_mult
 
        logic [2*MULT_ARITH_CFG.word_wdt-1:0] mult_res_full;
        logic [MULT_ARITH_CFG.word_wdt-1:0] mult_res_q;
        logic [2*MULT_ARITH_CFG.word_wdt-1:0] mult_op_in_del;
        logic mult_op_val_in_del;
        logic overflow_flag;

        del_chain //input registering
        #(
            .IN_WORD_WDT(2*MULT_ARITH_CFG.word_wdt),
            .DEL_CYC_LEN(MULT_IN_CYC_LEN)
        )
        in_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word({mult_op_a, mult_op_b}),
            .in_word_val(mult_op_val),
            .in_word_del(mult_op_in_del),
            .in_word_val_del(mult_op_val_in_del)
        );

        always_comb begin : mult_proc
            mult_res_full = $signed(mult_op_in_del[2*MULT_ARITH_CFG.word_wdt-1-:MULT_ARITH_CFG.word_wdt]) * $signed(mult_op_in_del[0+:MULT_ARITH_CFG.word_wdt]);

            //generate overflow bit
            overflow_flag = mult_res_full[2*MULT_ARITH_CFG.word_wdt-1] ? !(&mult_res_full[2*MULT_ARITH_CFG.word_wdt-1-:MULT_ARITH_CFG.fxp_cfg.int_wdt+1]) : |mult_res_full[2*MULT_ARITH_CFG.word_wdt-1-:MULT_ARITH_CFG.fxp_cfg.int_wdt+1];
            //normalize word to fit into original word length, perform saturation & rounding
            if(MULT_ARITH_CFG.arith_satur)
                if(overflow_flag)
                    mult_res_q = {mult_res_full[2*MULT_ARITH_CFG.word_wdt-1], {(MULT_ARITH_CFG.word_wdt-1){!mult_res_full[2*MULT_ARITH_CFG.word_wdt-1]}}}; //saturation
                else
                    mult_res_q = mult_res_full[MULT_ARITH_CFG.fxp_cfg.frac_wdt+:MULT_ARITH_CFG.word_wdt]; 
            else
                mult_res_q = mult_res_full[MULT_ARITH_CFG.fxp_cfg.frac_wdt+:MULT_ARITH_CFG.word_wdt]; 
        end

        del_chain //output registering
        #(
            .IN_WORD_WDT(MULT_ARITH_CFG.word_wdt),
            .DEL_CYC_LEN(MULT_OUT_CYC_LEN)
        )
        out_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word(mult_res_q),
            .in_word_val(mult_op_val_in_del),
            .in_word_del(mult_res),
            .in_word_val_del(mult_res_val)
        );

    end else if(MULT_ARITH_CFG.arith_type == FIXED_POINT_OPT_FPGA) begin

        logic [MULT_ARITH_CFG.word_wdt-1:0] mult_res_q;
        logic [2*MULT_ARITH_CFG.word_wdt-1:0] mult_res_full;
        logic [2*MULT_ARITH_CFG.word_wdt-1:0] mult_res_full_q;
        logic overflow_flag;

        dsp_macro_mult_18_bit fxp_mult
        (
          .CLK(clk),   
          .CE(clk_en), 
          .SCLR(!rst_n),
          .A(mult_op_a),        
          .B(mult_op_b),       
          .P(mult_res_full_q)        
        );

        del_chain //register for the valid bit
        #(
            .IN_WORD_WDT(1),
            .DEL_CYC_LEN(MULT_CYC_LEN)
        )
        in_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word(mult_op_val),
            .in_word_val(),
            .in_word_del(mult_res_val),
            .in_word_val_del()
        );

        del_chain //register the full output
        #(
            .IN_WORD_WDT(2*MULT_ARITH_CFG.word_wdt),
            .DEL_CYC_LEN(1)
        )
        mult_res_full_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word(mult_res_full_q),
            .in_word_val(),
            .in_word_del(mult_res_full),
            .in_word_val_del()
        );

        always_comb begin : satur_proc
            //generate overflow bit
            overflow_flag = mult_res_full[2*MULT_ARITH_CFG.word_wdt-1] ? !(&mult_res_full[2*MULT_ARITH_CFG.word_wdt-1-:MULT_ARITH_CFG.fxp_cfg.int_wdt+1]) : |mult_res_full[2*MULT_ARITH_CFG.word_wdt-1-:MULT_ARITH_CFG.fxp_cfg.int_wdt+1];
            //normalize word to fit into original word length, perform saturation & rounding
            if(MULT_ARITH_CFG.arith_satur)
                if(overflow_flag)
                    mult_res_q = {mult_res_full[2*MULT_ARITH_CFG.word_wdt-1], {(MULT_ARITH_CFG.word_wdt-1){!mult_res_full[2*MULT_ARITH_CFG.word_wdt-1]}}}; //saturation
                else
                    mult_res_q = mult_res_full[MULT_ARITH_CFG.fxp_cfg.frac_wdt+:MULT_ARITH_CFG.word_wdt]; 
            else
                mult_res_q = mult_res_full[MULT_ARITH_CFG.fxp_cfg.frac_wdt+:MULT_ARITH_CFG.word_wdt]; 
        end

        del_chain //output register
        #(
            .IN_WORD_WDT(MULT_ARITH_CFG.word_wdt),
            .DEL_CYC_LEN(1)
        )
        out_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word(mult_res_q),
            .in_word_val(), 
            .in_word_del(mult_res),
            .in_word_val_del()
        );
        
    end else if(MULT_ARITH_CFG.arith_type == ADDR_OPT_FPGA) begin

        del_chain //register for the valid bit
        #(
            .IN_WORD_WDT(1),
            .DEL_CYC_LEN(MULT_CYC_LEN)
        )
        val_in_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word(mult_op_val),
            .in_word_val(),
            .in_word_del(mult_res_val),
            .in_word_val_del()
        );

        logic [17:0] mult_op_a_i;
        logic [17:0] mult_op_b_i;
        logic [35:0] mult_res_i;

        always_comb begin //input width might not word width (output width), zero padd
            mult_op_a_i = '0;
            mult_op_b_i = '0;
            mult_op_a_i[15:0] = mult_op_a;
            mult_op_b_i[15:0] = mult_op_b;
        end

        dsp_macro_addr_mult_32_bit addr_mult 
        (
            .CLK(clk),   
            .CE(clk_en), 
            .SCLR(!rst_n),
            .A(mult_op_a_i),        
            .B(mult_op_b_i),       
            .P(mult_res_i)    
        );

        assign mult_res = mult_res_i[MULT_ARITH_CFG.word_wdt-1:0];
    end

endgenerate

endmodule