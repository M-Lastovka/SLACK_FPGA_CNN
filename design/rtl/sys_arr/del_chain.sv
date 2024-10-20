`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     del_chain
// Project Name:    Efficient FPGA CNN implementation
// Description:     simple chain of FFs parametrized by chain length and 
//                  word width, features clock enable, synchr. reset and valid bit
// Synthesizable:   Yes
//////////////////////////////////////////////////////////////////////////////////

module del_chain
#(
    parameter IN_WORD_WDT = 64,
    parameter DEL_CYC_LEN = 1
)
(
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    input  logic [IN_WORD_WDT-1:0] in_word,
    input  logic in_word_val,
    output logic [IN_WORD_WDT-1:0] in_word_del,
    output logic in_word_val_del
);

logic [IN_WORD_WDT-1:0] in_word_pipe_stage [DEL_CYC_LEN:0];
logic [IN_WORD_WDT-1:0] in_word_val_pipe_stage [DEL_CYC_LEN:0];

assign in_word_pipe_stage[0] = in_word;
assign in_word_val_pipe_stage[0] = in_word_val;

generate
    if(DEL_CYC_LEN == 0) begin : passthrough //do nothing

    end else begin : chain_delay
        always_ff @(posedge clk) begin
            if(!rst_n) begin
                for(int i = 1; i < DEL_CYC_LEN+1; i++) begin
                    in_word_pipe_stage[i] <= '0;
                    in_word_val_pipe_stage[i] <= 1'b0;
                end
            end else begin
                if(clk_en) begin
                    for(int i = 1; i < DEL_CYC_LEN+1; i++) begin
                        in_word_pipe_stage[i] <= in_word_pipe_stage[i-1];
                        in_word_val_pipe_stage[i] <= in_word_val_pipe_stage[i-1];
                    end
                end
            end
        end
    end
endgenerate

assign in_word_del = in_word_pipe_stage [DEL_CYC_LEN];
assign in_word_val_del = in_word_val_pipe_stage [DEL_CYC_LEN];

endmodule