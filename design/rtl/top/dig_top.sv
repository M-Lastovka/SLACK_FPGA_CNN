`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     dig_top
// Project Name:    Efficient FPGA CNN implementation
// Description:     design top
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;
import axi_if_pckg::*;
import perf_cnt_pckg::*;
import regmap_pckg::*;

module dig_top
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    //AXI stream slave interface
    input  logic [C_S_TDATA_WDT-1:0] S_AXIS_TDATA,
    input  logic [C_S_TKEEP_WDT-1:0] S_AXIS_TKEEP,
    input  logic S_AXIS_TLAST,
    input  logic S_AXIS_TVALID,	
    output logic S_AXIS_TREADY,
    //AXI stream master interface
    output  logic [C_M_TDATA_WDT-1:0]  M_AXIS_TDATA,
    output  logic [C_M_TKEEP_WDT-1:0]  M_AXIS_TKEEP,
    output  logic M_AXIS_TLAST,
    output  logic M_AXIS_TVALID,	
    input   logic M_AXIS_TREADY,
    //AXI-Lite interface
    //write address signals
    input  logic [C_S_AXI_ADDR_WDT-1:0] S_AXI_AWADDR, 
    input  logic [2:0] S_AXI_AWPROT, 
    input  logic S_AXI_AWVALID,
    output logic S_AXI_AWREADY,
    //write data signals
    input  logic [C_S_AXI_DATA_WDT-1:0] S_AXI_WDATA,
    input  logic [C_S_AXI_STRB_WDT-1:0] S_AXI_WSTRB,
    input  logic S_AXI_WVALID, 
    output logic S_AXI_WREADY,
    //write response signals
    output logic [1:0] S_AXI_BRESP, 
    output logic S_AXI_BVALID,
    input  logic S_AXI_BREADY,
    //read address signals
    input  logic [C_S_AXI_ADDR_WDT-1:0] S_AXI_ARADDR,
    input  logic [2:0] S_AXI_ARPROT, 
    input  logic S_AXI_ARVALID,
    output logic S_AXI_ARREADY,
    //read data signals
    output logic [C_S_AXI_DATA_WDT-1:0] S_AXI_RDATA,
    output logic [1:0] S_AXI_RRESP, 
    output logic S_AXI_RVALID,
    input  logic S_AXI_RREADY
);

tens_trans_spec_t sys_arr_tens_trans_spec_i;
tens_trans_spec_t batch_norm_tens_trans_spec_i;
tens_trans_spec_t nlin_f_tens_trans_spec_i;
tens_trans_spec_t maxpool_tens_trans_spec_i;
pipe_data_vect_t  sys_arr_data_fetch;
pipe_data_vect_t  sys_arr_data_out;
pipe_data_vect_t  batch_norm_data_fetch;
pipe_data_vect_t  batch_norm_data_out;
pipe_data_vect_t  nlin_f_data_fetch;
pipe_data_vect_t  nlin_f_data_out;
pipe_data_vect_t  maxpool_data_fetch;
pipe_data_vect_t  maxpool_data_out;
pipe_data_vect_t  mmem_if_rd_data_out;
pipe_data_vect_t  mmem_if_wr_data_in;
proc_pipe_ctrl_if sys_arr_pipe_ctrl_if();
proc_pipe_ctrl_if batch_norm_pipe_ctrl_if();
proc_pipe_ctrl_if nlin_f_pipe_ctrl_if();
proc_pipe_ctrl_if maxpool_pipe_ctrl_if();
block_ctrl_if     addr_gen_m_ctrl_if();
block_ctrl_if     addr_gen_wr_port_ctrl(); 
block_ctrl_if     addr_gen_rd_port_ctrl(); 
block_ctrl_if     m_axis_ctrl();
block_ctrl_if     s_axis_ctrl();
block_ctrl_if     main_fsm_s_ctrl_if();
block_ctrl_if     addr_gen_s_ctrl_if();
proc_pipe_ctrl_if addr_gen_rd_pipe_ctrl_if();
proc_pipe_ctrl_if addr_gen_wr_pipe_ctrl_if();
proc_pipe_ctrl_if mmem_if_rd_cmd_pipe_ctrl_if();
proc_pipe_ctrl_if mmem_if_wr_cmd_pipe_ctrl_if();
proc_pipe_ctrl_if mmem_if_rd_data_pipe_ctrl_if();
proc_pipe_ctrl_if mmem_if_wr_data_pipe_ctrl_if();
proc_pipe_ctrl_if m_axis_pipe_ctrl_if();
proc_pipe_ctrl_if s_axis_pipe_ctrl_if();
proc_pipe_ctrl_if mmem_if_ext_out_pipe_ctrl_if();
proc_pipe_ctrl_if mmem_if_ext_in_pipe_ctrl_if();
mem_cmd_rd_t      addr_gen_rd_mmem;
mem_cmd_wr_t      addr_gen_wr_mmem;
mem_cmd_rd_t      mmem_if_rd_cmd;
mem_cmd_wr_t      mmem_if_wr_cmd;
tens_trans_spec_t proc_pipe_tens_trans_spec;
pipe_data_vect_t  mmem_if_ext_wr_data_in;
pipe_data_vect_t  mmem_if_ext_rd_data_out;
pipe_data_vect_t  s_axis_data_out;
pipe_data_vect_t  m_axis_data_fetch;
tens_trans_spec_t tens_trans_spec;
logic [C_TENS_TRANS_SEQ_CNT_WDT-1:0] tens_trans_seq_cnt;
logic [C_TENS_TRANS_SEQ_CNT_WDT-1:0] tens_trans_seq_lim;
logic soft_rst;
logic [C_PERF_CNT_CNT-1:0] perf_cnt_step_fsm;
logic [C_PERF_CNT_CNT-1:0] perf_cnt_step_addr_gen;
logic sys_rst_n;

regmap_rd_if
#(
    .ADDR_WDT(C_S_AXI_ADDR_WDT),
    .DATA_WDT(C_REGMAP_DATA_WDT)
)
main_fsm_regmap_rd_if ();

regmap_rd_if
#(
    .ADDR_WDT(C_S_AXI_ADDR_WDT),
    .DATA_WDT(C_REGMAP_DATA_WDT)
)
s_axil_regmap_rd_if ();

regmap_wr_if
#(
    .ADDR_WDT(C_S_AXI_ADDR_WDT),
    .DATA_WDT(C_REGMAP_DATA_WDT)
)
s_axil_regmap_wr_if ();

rst_gen rst_gen_inst
(
    .clk(clk),
    .rst_n(rst_n),
    .soft_rst(soft_rst),
    .sys_rst_n(sys_rst_n)
);

s_axil s_axil_inst
(
    .S_AXI_ACLK         (clk                ),
    .S_AXI_ARESETN      (sys_rst_n          ),
    .S_AXI_AWADDR       (S_AXI_AWADDR       ), 
    .S_AXI_AWPROT       (S_AXI_AWPROT       ), 
    .S_AXI_AWVALID      (S_AXI_AWVALID      ),
    .S_AXI_AWREADY      (S_AXI_AWREADY      ),
    .S_AXI_WDATA        (S_AXI_WDATA        ),
    .S_AXI_WSTRB        (S_AXI_WSTRB        ),
    .S_AXI_WVALID       (S_AXI_WVALID       ), 
    .S_AXI_WREADY       (S_AXI_WREADY       ),
    .S_AXI_BRESP        (S_AXI_BRESP        ), 
    .S_AXI_BVALID       (S_AXI_BVALID       ),
    .S_AXI_BREADY       (S_AXI_BREADY       ),
    .S_AXI_ARADDR       (S_AXI_ARADDR       ),
    .S_AXI_ARPROT       (S_AXI_ARPROT       ), 
    .S_AXI_ARVALID      (S_AXI_ARVALID      ),
    .S_AXI_ARREADY      (S_AXI_ARREADY      ),
    .S_AXI_RDATA        (S_AXI_RDATA        ),
    .S_AXI_RRESP        (S_AXI_RRESP        ), 
    .S_AXI_RVALID       (S_AXI_RVALID       ),
    .S_AXI_RREADY       (S_AXI_RREADY       ),
    .s_axil_regmap_rd_if(s_axil_regmap_rd_if),
    .s_axil_regmap_wr_if(s_axil_regmap_wr_if)
);

regmap regmap_inst
(
    .clk                    (clk                  ),
    .rst_n                  (sys_rst_n            ),
    .soft_rst               (soft_rst             ),
    .s_axil_regmap_rd_if    (s_axil_regmap_rd_if  ),
    .s_axil_regmap_wr_if    (s_axil_regmap_wr_if  ),
    .main_fsm_regmap_rd_if  (main_fsm_regmap_rd_if),
    .perf_cnt_step_fsm      (perf_cnt_step_fsm ),
    .tens_trans_seq_cnt     (tens_trans_seq_cnt   ),
    .tens_trans_seq_lim     (tens_trans_seq_lim   ),
    .main_fsm_s_ctrl_if     (main_fsm_s_ctrl_if   )
);

main_fsm main_fsm_inst
(
    .clk                            (clk                         ),
    .rst_n                          (sys_rst_n                   ),
    .perf_cnt_step_fsm              (perf_cnt_step_fsm           ),
    .perf_cnt_step_addr_gen         (perf_cnt_step_addr_gen      ),
    .tens_trans_spec                (tens_trans_spec             ),
    .main_fsm_regmap_rd_if          (main_fsm_regmap_rd_if       ),
    .tens_trans_seq_cnt             (tens_trans_seq_cnt          ),
    .tens_trans_seq_lim             (tens_trans_seq_lim          ),
    .addr_gen_s_ctrl_if             (addr_gen_s_ctrl_if          ),
    .main_fsm_s_ctrl_if             (main_fsm_s_ctrl_if          ),
    .maxpool_pipe_ctrl_if           (maxpool_pipe_ctrl_if        ),
    .sys_arr_pipe_ctrl_if           (sys_arr_pipe_ctrl_if        ), 
    .batch_norm_pipe_ctrl_if        (batch_norm_pipe_ctrl_if     ),
    .nlin_f_pipe_ctrl_if            (nlin_f_pipe_ctrl_if         ),
    .addr_gen_rd_pipe_ctrl_if       (addr_gen_rd_pipe_ctrl_if    ),
    .addr_gen_wr_pipe_ctrl_if       (addr_gen_wr_pipe_ctrl_if    ),
    .mmem_if_rd_cmd_pipe_ctrl_if    (mmem_if_rd_cmd_pipe_ctrl_if ),
    .mmem_if_wr_cmd_pipe_ctrl_if    (mmem_if_wr_cmd_pipe_ctrl_if ),
    .mmem_if_rd_data_pipe_ctrl_if   (mmem_if_rd_data_pipe_ctrl_if),
    .mmem_if_wr_data_pipe_ctrl_if   (mmem_if_wr_data_pipe_ctrl_if),
    .m_axis_pipe_ctrl_if            (m_axis_pipe_ctrl_if         ),
    .s_axis_pipe_ctrl_if            (s_axis_pipe_ctrl_if         ),
    .mmem_if_ext_out_pipe_ctrl_if   (mmem_if_ext_out_pipe_ctrl_if),
    .mmem_if_ext_in_pipe_ctrl_if    (mmem_if_ext_in_pipe_ctrl_if )
);

s_axis s_axis_inst
(
    .S_AXIS_ACLK(clk),
    .S_AXIS_ARESETN(sys_rst_n),
    .S_AXIS_TDATA(S_AXIS_TDATA),
    .S_AXIS_TKEEP(S_AXIS_TKEEP),
    .S_AXIS_TLAST(S_AXIS_TLAST),
    .S_AXIS_TVALID(S_AXIS_TVALID),	
    .S_AXIS_TREADY(S_AXIS_TREADY),
    .s_axis_pipe_ctrl_if(s_axis_pipe_ctrl_if),
    .s_axis_ctrl(s_axis_ctrl),
    .stream_in_padding(tens_trans_spec.tens_trans_cfg.conv_cfg.conv_padding_0),
    .s_axis_data_out(s_axis_data_out)
);

pipe_fifo
#(
    .WORD_WDT($bits(mmem_if_ext_wr_data_in)),
    .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH)
)
pipe_fifo_bpress_mmem_ext_data_in
(
    .clk                        (clk                              ),
    .rst_n                      (sys_rst_n                        ),
    .upstream_pipe_ctrl_if      (s_axis_pipe_ctrl_if              ),
    .downstream_pipe_ctrl_if    (mmem_if_ext_in_pipe_ctrl_if      ),
    .upstream_word              (s_axis_data_out                  ),
    .upstream_word_val          (s_axis_data_out.data_vect_val    ),
    .downstream_word            (mmem_if_ext_wr_data_in           ),
    .downstream_word_val        ()
);

pipe_fifo
#(
    .WORD_WDT($bits(mmem_if_ext_rd_data_out)),
    .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH)
)
pipe_fifo_bpress_mmem_ext_data_out
(
    .clk                        (clk                                  ),
    .rst_n                      (sys_rst_n                            ),
    .upstream_pipe_ctrl_if      (mmem_if_ext_out_pipe_ctrl_if         ),
    .downstream_pipe_ctrl_if    (m_axis_pipe_ctrl_if                  ),
    .upstream_word              (mmem_if_ext_rd_data_out              ),
    .upstream_word_val          (mmem_if_ext_rd_data_out.data_vect_val),
    .downstream_word            (m_axis_data_fetch                    ),
    .downstream_word_val        ()
);

m_axis m_axis_inst
(
    .M_AXIS_ACLK(clk),
    .M_AXIS_ARESETN(sys_rst_n),
    .M_AXIS_TDATA(M_AXIS_TDATA),
    .M_AXIS_TKEEP(M_AXIS_TKEEP),
    .M_AXIS_TLAST(M_AXIS_TLAST),
    .M_AXIS_TVALID(M_AXIS_TVALID),	
    .M_AXIS_TREADY(M_AXIS_TREADY),
    .m_axis_pipe_ctrl_if(m_axis_pipe_ctrl_if),
    .m_axis_ctrl(m_axis_ctrl),
    .stream_out_padding(tens_trans_spec.tens_trans_cfg.conv_cfg.conv_padding_1),
    .m_axis_data_fetch(m_axis_data_fetch)
);

pipe_fifo
#(
    .WORD_WDT($bits(addr_gen_rd_mmem)),
    .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH)
)
pipe_fifo_bpress_addr_gen_rd
(
    .clk                        (clk                       ),
    .rst_n                      (sys_rst_n                     ),
    .upstream_pipe_ctrl_if      (addr_gen_rd_pipe_ctrl_if  ),
    .downstream_pipe_ctrl_if    (mmem_if_rd_cmd_pipe_ctrl_if      ),
    .upstream_word              (addr_gen_rd_mmem          ),
    .upstream_word_val          (addr_gen_rd_mmem.cmd_rd_en),
    .downstream_word            (mmem_if_rd_cmd               ),
    .downstream_word_val        ()
);

pipe_fifo
#(
    .WORD_WDT($bits(addr_gen_wr_mmem)),
    .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH)
)
pipe_fifo_bpress_addr_gen_wr
(
    .clk                        (clk                       ),
    .rst_n                      (sys_rst_n                     ),
    .upstream_pipe_ctrl_if      (addr_gen_wr_pipe_ctrl_if  ),
    .downstream_pipe_ctrl_if    (mmem_if_wr_cmd_pipe_ctrl_if ),
    .upstream_word              (addr_gen_wr_mmem          ),
    .upstream_word_val          (addr_gen_wr_mmem.cmd_wr_en),
    .downstream_word            (mmem_if_wr_cmd               ),
    .downstream_word_val        ()
);

mmem_if mmem_if_inst
(
    .clk                          (clk                         ),
    .rst_n                        (sys_rst_n                       ),
    .mmem_if_rd_cmd_pipe_ctrl_if  (mmem_if_rd_cmd_pipe_ctrl_if ),
    .mmem_if_rd_data_pipe_ctrl_if (mmem_if_rd_data_pipe_ctrl_if),
    .mmem_if_wr_cmd_pipe_ctrl_if  (mmem_if_wr_cmd_pipe_ctrl_if ),
    .mmem_if_wr_data_pipe_ctrl_if (mmem_if_wr_data_pipe_ctrl_if),
    .mmem_if_ext_out_pipe_ctrl_if (mmem_if_ext_out_pipe_ctrl_if),
    .mmem_if_ext_in_pipe_ctrl_if  (mmem_if_ext_in_pipe_ctrl_if ),
    .addr_gen_wr_port_ctrl        (addr_gen_wr_port_ctrl),
    .addr_gen_rd_port_ctrl        (addr_gen_rd_port_ctrl),
    .m_axis_ctrl                  (m_axis_ctrl          ),
    .mmem_if_rd_cmd               (mmem_if_rd_cmd         ),
    .mmem_if_rd_data_out          (mmem_if_rd_data_out    ),
    .mmem_if_wr_cmd               (mmem_if_wr_cmd         ),
    .mmem_if_wr_data_in           (mmem_if_wr_data_in     ),
    .mmem_if_ext_rd_data_out      (mmem_if_ext_rd_data_out     ),
    .mmem_if_ext_wr_data_in       (mmem_if_ext_wr_data_in      )
);

addr_gen addr_gen_inst
(
    .clk                        (clk                        ),
    .rst_n                      (sys_rst_n                  ),
    .addr_gen_s_ctrl_if         (addr_gen_s_ctrl_if         ),
    .addr_gen_m_ctrl_if         (addr_gen_m_ctrl_if         ),
    .addr_gen_wr_port_ctrl      (addr_gen_wr_port_ctrl      ),
    .addr_gen_rd_port_ctrl      (addr_gen_rd_port_ctrl      ),
    .addr_gen_rd_pipe_ctrl_if   (addr_gen_rd_pipe_ctrl_if   ),
    .addr_gen_wr_pipe_ctrl_if   (addr_gen_wr_pipe_ctrl_if   ),
    .s_axis_ctrl                (s_axis_ctrl                ),
    .tens_trans_spec            (tens_trans_spec            ),
    .proc_pipe_tens_trans_spec  (proc_pipe_tens_trans_spec  ),
    .perf_cnt_step_addr_gen     (perf_cnt_step_addr_gen     ),
    .addr_gen_rd_mmem           (addr_gen_rd_mmem           ),
    .addr_gen_wr_mmem           (addr_gen_wr_mmem           )
);

pipe_fifo
#(
    .WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH)
)
pipe_fifo_bpress_sys_arr
(
    .clk                        (clk                    ),
    .rst_n                      (sys_rst_n                  ),
    .upstream_pipe_ctrl_if      (mmem_if_rd_data_pipe_ctrl_if  ),
    .downstream_pipe_ctrl_if    (sys_arr_pipe_ctrl_if   ),
    .upstream_word              (mmem_if_rd_data_out                ),
    .upstream_word_val          (mmem_if_rd_data_out.data_vect_val  ),
    .downstream_word            (sys_arr_data_fetch     ),
    .downstream_word_val        ()
);

sys_arr sys_arr_inst
(
    .clk                        (clk),
    .rst_n                      (sys_rst_n),
    .sys_arr_ctrl_if            (addr_gen_m_ctrl_if),
    .sys_arr_pipe_ctrl_if       (sys_arr_pipe_ctrl_if),
    .sys_arr_tens_trans_spec    (proc_pipe_tens_trans_spec),
    .sys_arr_tens_trans_spec_i  (sys_arr_tens_trans_spec_i),
    .sys_arr_tens_trans_lin_dims(proc_pipe_tens_trans_spec.tens_trans_lin_dims),
    .sys_arr_data_fetch         (sys_arr_data_fetch),
    .sys_arr_data_out           (sys_arr_data_out)
);

pipe_fifo
#(
    .WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH)
)
pipe_fifo_bpress_batch_norm
(
    .clk                        (clk                                 ),
    .rst_n                      (sys_rst_n                           ),
    .upstream_pipe_ctrl_if      (sys_arr_pipe_ctrl_if                ),
    .downstream_pipe_ctrl_if    (batch_norm_pipe_ctrl_if             ),
    .upstream_word              (sys_arr_data_out                    ),
    .upstream_word_val          (sys_arr_data_out.data_vect_val      ),
    .downstream_word            (batch_norm_data_fetch               ),
    .downstream_word_val        ()
);

batch_norm_unit batch_norm_unit_inst
(
    .clk                            (clk),
    .rst_n                          (sys_rst_n),
    .batch_norm_pipe_ctrl_if        (batch_norm_pipe_ctrl_if),
    .batch_norm_tens_trans_spec     (sys_arr_tens_trans_spec_i),
    .batch_norm_tens_trans_spec_i   (batch_norm_tens_trans_spec_i),
    .batch_norm_data_fetch          (batch_norm_data_fetch),
    .batch_norm_data_out            (batch_norm_data_out)
);

pipe_fifo
#(
    .WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH)
)
pipe_fifo_bpress_nlin_f
(
    .clk                        (clk                                ),
    .rst_n                      (sys_rst_n                          ),
    .upstream_pipe_ctrl_if      (batch_norm_pipe_ctrl_if            ),
    .downstream_pipe_ctrl_if    (nlin_f_pipe_ctrl_if                ),
    .upstream_word              (batch_norm_data_out                ),
    .upstream_word_val          (batch_norm_data_out.data_vect_val  ),
    .downstream_word            (nlin_f_data_fetch                  ),
    .downstream_word_val        ()
);

nlin_f_unit nlin_f_unit_inst
(
    .clk                        (clk                                ),
    .rst_n                      (sys_rst_n                          ),
    .nlin_f_pipe_ctrl_if        (nlin_f_pipe_ctrl_if                ),
    .nlin_f_tens_trans_spec     (batch_norm_tens_trans_spec_i       ),
    .nlin_f_tens_trans_spec_i   (nlin_f_tens_trans_spec_i           ),
    .nlin_f_data_fetch          (nlin_f_data_fetch                  ),
    .nlin_f_data_out            (nlin_f_data_out                    )
);

pipe_fifo
#(
    .WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH)
)
pipe_fifo_bpress_maxpool
(
    .clk                        (clk                                ),
    .rst_n                      (sys_rst_n                          ),
    .upstream_pipe_ctrl_if      (nlin_f_pipe_ctrl_if                ),
    .downstream_pipe_ctrl_if    (maxpool_pipe_ctrl_if       ),
    .upstream_word              (nlin_f_data_out                    ),
    .upstream_word_val          (nlin_f_data_out.data_vect_val      ),
    .downstream_word            (maxpool_data_fetch                 ),
    .downstream_word_val        ()
);

maxpool_unit maxpool_unit_inst
(
    .clk                        (clk                      ),
    .rst_n                      (sys_rst_n                ),
    .maxpool_pipe_ctrl_if       (maxpool_pipe_ctrl_if     ),
    .maxpool_tens_trans_spec    (nlin_f_tens_trans_spec_i ),
    .maxpool_tens_trans_spec_i  (maxpool_tens_trans_spec_i),
    .maxpool_data_fetch         (maxpool_data_fetch       ),
    .maxpool_data_out           (maxpool_data_out         )
);

pipe_fifo
#(
    .WORD_WDT(C_PIPE_DATA_VECT_WDT),
    .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH)
)
pipe_fifo_bpress_mmem_wr_data
(
    .clk                        (clk                                ),
    .rst_n                      (sys_rst_n                          ),
    .upstream_pipe_ctrl_if      (maxpool_pipe_ctrl_if               ),
    .downstream_pipe_ctrl_if    (mmem_if_wr_data_pipe_ctrl_if       ),
    .upstream_word              (maxpool_data_out                   ),
    .upstream_word_val          (maxpool_data_out.data_vect_val     ),
    .downstream_word            (mmem_if_wr_data_in                 ),
    .downstream_word_val        (                                   )
);

endmodule