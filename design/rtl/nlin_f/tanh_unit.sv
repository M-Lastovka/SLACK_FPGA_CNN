`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     nlin_f_unit
// Project Name:    Efficient FPGA CNN implementation
// Description:     Block for computing tanh
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;

module tanh_unit
(
    //clk&reset
    input clk,
    input rst_n,
    input clk_en,
    //data
    input  pipe_data_t tanh_op,
    output pipe_data_t tanh_res

);

localparam logic [C_ARITH_WORD_LEN-1:0] FXP_TANH_SATUR_VALUE = (1 << C_ARITH_FXP_FRAC_WDT);

//-------------------------------------------------------------
//Inputs register----------------------------------------------
//-------------------------------------------------------------

pipe_data_t tanh_op_del;
pipe_data_t tanh_op_del_i;

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_WDT),
    .DEL_CYC_LEN(C_TANH_IN_DEL_CYC_LEN)
)
tanh_in_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(tanh_op),
    .in_word_val(),
    .in_word_del(tanh_op_del),
    .in_word_val_del()
);

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_WDT),
    .DEL_CYC_LEN(2)
)
tanh_op_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(tanh_op_del),
    .in_word_val(),
    .in_word_del(tanh_op_del_i),
    .in_word_val_del()
);

logic tanh_op_val;
logic tanh_op_val_i;
logic tanh_op_sgn_q;
logic tanh_op_lin_phase_q;
logic tanh_op_sat_phase_q;
logic tanh_op_sgn;
logic tanh_op_lin_phase;
logic tanh_op_sat_phase;
logic tanh_op_sgn_i;
logic tanh_op_lin_phase_i;
logic tanh_op_sat_phase_i;
logic [C_ARITH_WORD_LEN-1:0] tanh_op_abs;
logic [C_ARITH_WORD_LEN-1:0] tanh_op_abs_offset;
logic tanh_lut_en;
logic [C_TANH_LUT_MEM_DATA_WDT-1:0]  tanh_lut_mem[C_TANH_LUT_MEM_SIZE-1:0];
logic [C_TANH_LUT_MEM_DATA_WDT-1:0]  tanh_lut_out;
logic [C_TANH_LUT_MEM_ADDR_WDT-1:0]  tanh_lut_mem_addr;

//----------------------------------------------------------------------------
//preparing of data, resolving phase------------------------------------------
//----------------------------------------------------------------------------
always_comb begin : tanh_phase_resolve 
    tanh_op_sgn_q = tanh_op_del.data_word[C_ARITH_WORD_LEN-1];
    tanh_op_abs = tanh_op_sgn_q ? -tanh_op_del.data_word : tanh_op_del.data_word;
    tanh_op_abs_offset = tanh_op_abs - C_TANH_LIN_END;
    tanh_op_lin_phase_q = tanh_op_abs <= C_TANH_LIN_END;
    tanh_op_sat_phase_q = tanh_op_abs >= C_TANH_SAT_START;
end
always_ff @(posedge clk) begin : tanh_phase_resolve_reg
    if(!rst_n) begin
        tanh_op_sgn               <= 1'b0;
        tanh_op_lin_phase         <= 1'b0;
        tanh_op_sat_phase         <= 1'b0;
        tanh_op_sgn_i             <= 1'b0;
        tanh_op_lin_phase_i       <= 1'b0;
        tanh_op_sat_phase_i       <= 1'b0;
        tanh_lut_mem_addr         <= '0;
        tanh_op_val               <= 1'b0;
        tanh_op_val_i             <= 1'b0;
    end else begin
        if(clk_en) begin
            tanh_op_sgn               <= tanh_op_sgn_q;
            tanh_op_lin_phase         <= tanh_op_lin_phase_q;
            tanh_op_sat_phase         <= tanh_op_sat_phase_q;
            tanh_op_sgn_i             <= tanh_op_sgn;
            tanh_op_lin_phase_i       <= tanh_op_lin_phase;
            tanh_op_sat_phase_i       <= tanh_op_sat_phase;
            tanh_lut_mem_addr         <= tanh_op_abs_offset[$clog2(C_TANH_DOWN_SA_FACT) +: C_TANH_LUT_MEM_ADDR_WDT];
            tanh_op_val               <= tanh_op_del.data_val;
            tanh_op_val_i             <= tanh_op_val;
        end
    end
end

//----------------------------------------------------------------------------
//LUT-------------------------------------------------------------------------
//----------------------------------------------------------------------------

initial begin
    $readmemb(C_TANH_LUT_PATH, tanh_lut_mem);
end
assign tanh_lut_en = !tanh_op_lin_phase & !tanh_op_sat_phase & clk_en & tanh_op_val;
always_ff @(posedge clk) begin : tanh_lut_read
    if(tanh_lut_en)
        tanh_lut_out <= tanh_lut_mem[tanh_lut_mem_addr];
end

//----------------------------------------------------------------------------
//Final MUX-------------------------------------------------------------------
//----------------------------------------------------------------------------

pipe_data_t tanh_op_res_q;

always_comb begin : res_mux
    casez ({tanh_op_val_i, tanh_op_lin_phase_i, tanh_op_sat_phase_i})
        3'b100:  tanh_op_res_q.data_word = tanh_op_sgn_i ? -tanh_lut_out : tanh_lut_out;
        3'b101:  tanh_op_res_q.data_word = tanh_op_sgn_i ? -FXP_TANH_SATUR_VALUE : FXP_TANH_SATUR_VALUE;
        3'b110:  tanh_op_res_q.data_word = tanh_op_del_i.data_word;
        default: tanh_op_res_q.data_word = C_PIPE_DATA_RST_VAL;
    endcase
    tanh_op_res_q.data_type  = tanh_op_del_i.data_type;
    tanh_op_res_q.data_val   = tanh_op_del_i.data_val;
    tanh_op_res_q.data_last  = tanh_op_del_i.data_last;
end

del_chain
#(
    .IN_WORD_WDT(C_PIPE_DATA_WDT),
    .DEL_CYC_LEN(C_TANH_OUT_DEL_CYC_LEN)
)
tanh_out_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(tanh_op_res_q),
    .in_word_val(),
    .in_word_del(tanh_res),
    .in_word_val_del()
);

// synthesis translate_off

//simple immediate assertions
always_ff @(posedge clk) assert (!(tanh_op_lin_phase & tanh_op_sat_phase) | !rst_n) else $error("Tanh input shall never be both in linear and in saturation phase");

// synthesis translate_on

endmodule
