`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     rst_gen
// Project Name:    Efficient FPGA CNN implementation
// Description:     generate the system reset (active low), buffers the external and 
//                  internal reset signals, intended for FPGA
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

module rst_gen
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    input  logic soft_rst,
    output logic sys_rst_n
);

logic sys_rst_n_q;
logic sys_rst_n_i = 1'b1;

assign sys_rst_n_q = !(!rst_n | soft_rst);

always_ff @(posedge clk) begin : rst_gen_reg
    sys_rst_n_i <= sys_rst_n_q;
end

assign sys_rst_n = sys_rst_n_i;

endmodule