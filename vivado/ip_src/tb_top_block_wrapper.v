//Copyright 1986-2021 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2021.1 (win64) Build 3247384 Thu Jun 10 19:36:33 MDT 2021
//Date        : Mon Aug 26 11:59:56 2024
//Host        : DESKTOP-2Q64EM4 running 64-bit major release  (build 9200)
//Command     : generate_target tb_top_block_wrapper.bd
//Design      : tb_top_block_wrapper
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

module tb_top_block_wrapper
   (clk,
    rst_n);
  input clk;
  input rst_n;

  wire clk;
  wire rst_n;

  tb_top_block tb_top_block_i
       (.clk(clk),
        .rst_n(rst_n));
endmodule
