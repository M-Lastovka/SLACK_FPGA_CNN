#!/usr/bin/env python3
# -*- coding: utf-8 -*-

""" Created with Corsair v1.0.4

Control/status register map.
"""

import struct

class interface:
    def __init__(self, regmap_size, fd):
        # Initialize reg_map_mem with a static size of 32 and 32-bit integers (using a list)
        self.reg_map_mem = [0] * regmap_size
        self.fd = fd

    def write(self, address, value):
        """Writes a value to the reg_map_mem at the specified address."""
        if not (0 <= address < len(self.reg_map_mem)):
            raise ValueError("Address out of range")
        if not (0 <= value <= 0xFFFFFFFF):
            raise ValueError("Value out of range. Must be a 32-bit integer.")
        if not (address % 4 == 0):
            raise ValueError("Unaligned addresses not allowed.")
        self.reg_map_mem[address] = value

    def read(self, address):
        """Reads a value from the reg_map_mem at the specified address."""
        if not (0 <= address < len(self.reg_map_mem)):
            raise ValueError("Address out of range")
        if not (address % 4 == 0):
            raise ValueError("Unaligned addresses not allowed.")
        return self.reg_map_mem[address]
    
    def dump_state(self, start_addr, end_addr, eob = False, offset = 0):
        for addr in range(start_addr, end_addr + 4, 4):
            self.fd.write(struct.pack('>c', b'\x01'))  #write
            self.fd.write(struct.pack('>I', addr + offset))
            self.fd.write(struct.pack('>I', self.reg_map_mem[addr])) 
            self.fd.write(struct.pack('>c', b'\xff'))  #strobes are always 1s
        if(eob):
            self.fd.write(struct.pack('>c', b'\x00'))  #write
            self.fd.write(struct.pack('>I', 0x00))
            self.fd.write(struct.pack('>I', 0x00)) 
            self.fd.write(struct.pack('>c', b'\x00'))  #strobes are always 1s

    def read_state(self, start_addr, end_addr, eob = False):
        for addr in range(start_addr, end_addr + 4, 4):
            self.fd.write(struct.pack('>c', b'\x00'))  #read
            self.fd.write(struct.pack('>I', addr))
            self.fd.write(struct.pack('>I', 0x00)) 
            self.fd.write(struct.pack('>c', b'\xff'))
        if(eob):
            self.fd.write(struct.pack('>c', b'\x00'))  #write
            self.fd.write(struct.pack('>I', 0x00))
            self.fd.write(struct.pack('>I', 0x00)) 
            self.fd.write(struct.pack('>c', b'\x00'))  #strobes are always 1s


class _RegCnn_accel_ctrl_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_trans_seq_start(self):
        """write to start the tensor trans. sequence, if enabled"""
        return 0

    @tens_trans_seq_start.setter
    def tens_trans_seq_start(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_START_MSK << self._rmap.CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_START_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_START_MSK) << self._rmap.CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_START_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_CTRL_REG_ADDR, rdata)

    @property
    def tens_trans_seq_len(self):
        """length of the tensor trans. sequence"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_CTRL_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_POS) & self._rmap.CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_MSK

    @tens_trans_seq_len.setter
    def tens_trans_seq_len(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_MSK << self._rmap.CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_MSK) << self._rmap.CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_CTRL_REG_ADDR, rdata)

    @property
    def soft_reset(self):
        """software reset"""
        return 0

    @soft_reset.setter
    def soft_reset(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_CTRL_REG_SOFT_RESET_MSK << self._rmap.CNN_ACCEL_CTRL_REG_SOFT_RESET_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_CTRL_REG_SOFT_RESET_MSK) << self._rmap.CNN_ACCEL_CTRL_REG_SOFT_RESET_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_CTRL_REG_ADDR, rdata)


class _RegCnn_accel_stat_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_trans_seq_busy(self):
        """tensor trans. sequence is progressing"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_STAT_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_BUSY_POS) & self._rmap.CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_BUSY_MSK

    @property
    def tens_trans_seq_cnt(self):
        """index of the current trans. sequence in progress"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_STAT_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_CNT_POS) & self._rmap.CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_CNT_MSK

class _RegCnn_accel_int_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def int_tens_trans_seq_done_en(self):
        """interrupt enable - tensor transformation sequence done"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_POS) & self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_MSK

    @int_tens_trans_seq_done_en.setter
    def int_tens_trans_seq_done_en(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_MSK << self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_MSK) << self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_INT_REG_ADDR, rdata)

    @property
    def int_tens_trans_seq_done_stat(self):
        """interrupt status - tensor transformation sequence done"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_POS) & self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_MSK

    @property
    def int_tens_trans_seq_done_clear(self):
        """interrupt clear - tensor transformation sequence done"""
        return 0

    @int_tens_trans_seq_done_clear.setter
    def int_tens_trans_seq_done_clear(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_MSK << self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_MSK) << self._rmap.CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_INT_REG_ADDR, rdata)

    @property
    def int_stream_h2c_done_en(self):
        """interrupt enable - tensor transformation sequence done"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_POS) & self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_MSK

    @int_stream_h2c_done_en.setter
    def int_stream_h2c_done_en(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_MSK << self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_MSK) << self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_INT_REG_ADDR, rdata)

    @property
    def int_stream_h2c_done_stat(self):
        """interrupt status - tensor transformation sequence done"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_STAT_POS) & self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_STAT_MSK

    @property
    def int_stream_h2c_done_clear(self):
        """interrupt clear - tensor transformation sequence done"""
        return 0

    @int_stream_h2c_done_clear.setter
    def int_stream_h2c_done_clear(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_CLEAR_MSK << self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_CLEAR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_CLEAR_MSK) << self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_CLEAR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_INT_REG_ADDR, rdata)

    @property
    def int_stream_c2h_done_en(self):
        """interrupt enable - tensor transformation sequence done"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_POS) & self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_MSK

    @int_stream_c2h_done_en.setter
    def int_stream_c2h_done_en(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_MSK << self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_MSK) << self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_INT_REG_ADDR, rdata)

    @property
    def int_stream_c2h_done_stat(self):
        """interrupt status - tensor transformation sequence done"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_STAT_POS) & self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_STAT_MSK

    @property
    def int_stream_c2h_done_clear(self):
        """interrupt clear - tensor transformation sequence done"""
        return 0

    @int_stream_c2h_done_clear.setter
    def int_stream_c2h_done_clear(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_INT_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_CLEAR_MSK << self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_CLEAR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_CLEAR_MSK) << self._rmap.CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_CLEAR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_INT_REG_ADDR, rdata)

class _RegCnn_accel_mmem_offset_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def mmem_offset(self):
        """address offset"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_MMEM_OFFSET_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_POS) & self._rmap.CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_MSK

    @mmem_offset.setter
    def mmem_offset(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_MMEM_OFFSET_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_MSK << self._rmap.CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_MSK) << self._rmap.CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_MMEM_OFFSET_REG_ADDR, rdata)

class _RegCnn_accel_gp_rw_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def gp_rw(self):
        """general purpose register"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_GP_RW_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_GP_RW_REG_GP_RW_POS) & self._rmap.CNN_ACCEL_GP_RW_REG_GP_RW_MSK

    @gp_rw.setter
    def gp_rw(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_GP_RW_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_GP_RW_REG_GP_RW_MSK << self._rmap.CNN_ACCEL_GP_RW_REG_GP_RW_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_GP_RW_REG_GP_RW_MSK) << self._rmap.CNN_ACCEL_GP_RW_REG_GP_RW_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_GP_RW_REG_ADDR, rdata)

class _RegCnn_accel_perf_run_ctrl_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_run_en(self):
        """perf. counter enable"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_POS) & self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_MSK

    @perf_run_en.setter
    def perf_run_en(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_MSK << self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_MSK) << self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_ADDR, rdata)

    @property
    def perf_run_clear(self):
        """perf. counter clear"""
        return 0

    @perf_run_clear.setter
    def perf_run_clear(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_MSK << self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_MSK) << self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_PERF_RUN_CTRL_REG_ADDR, rdata)


class _RegCnn_accel_perf_run_lh_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_run_lh(self):
        """perf. counter value"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_RUN_LH_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_RUN_LH_REG_PERF_RUN_LH_POS) & self._rmap.CNN_ACCEL_PERF_RUN_LH_REG_PERF_RUN_LH_MSK


class _RegCnn_accel_perf_run_uh_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_run_uh(self):
        """perf. counter value"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_RUN_UH_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_RUN_UH_REG_PERF_RUN_UH_POS) & self._rmap.CNN_ACCEL_PERF_RUN_UH_REG_PERF_RUN_UH_MSK


class _RegCnn_accel_perf_comp_ctrl_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_comp_en(self):
        """perf. counter enable"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_POS) & self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_MSK

    @perf_comp_en.setter
    def perf_comp_en(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_MSK << self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_MSK) << self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_ADDR, rdata)

    @property
    def perf_comp_clear(self):
        """perf. counter clear"""
        return 0

    @perf_comp_clear.setter
    def perf_comp_clear(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_MSK << self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_MSK) << self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_PERF_COMP_CTRL_REG_ADDR, rdata)


class _RegCnn_accel_perf_comp_lh_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_comp_lh(self):
        """perf. counter value"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_COMP_LH_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_COMP_LH_REG_PERF_COMP_LH_POS) & self._rmap.CNN_ACCEL_PERF_COMP_LH_REG_PERF_COMP_LH_MSK


class _RegCnn_accel_perf_comp_uh_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_comp_uh(self):
        """perf. counter value"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_COMP_UH_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_COMP_UH_REG_PERF_COMP_UH_POS) & self._rmap.CNN_ACCEL_PERF_COMP_UH_REG_PERF_COMP_UH_MSK


class _RegCnn_accel_perf_stream_c2h_ctrl_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_stream_en(self):
        """perf. counter enable"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_POS) & self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_MSK

    @perf_stream_en.setter
    def perf_stream_en(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_MSK << self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_MSK) << self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_ADDR, rdata)

    @property
    def perf_stream_clear(self):
        """perf. counter clear"""
        return 0

    @perf_stream_clear.setter
    def perf_stream_clear(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_MSK << self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_MSK) << self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_ADDR, rdata)


class _RegCnn_accel_perf_stream_c2h_lh_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_stream_lh(self):
        """perf. counter value"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_STREAM_C2H_LH_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_POS) & self._rmap.CNN_ACCEL_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_MSK


class _RegCnn_accel_perf_stream_c2h_uh_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_stream_uh(self):
        """perf. counter value"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_STREAM_C2H_UH_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_POS) & self._rmap.CNN_ACCEL_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_MSK


class _RegCnn_accel_perf_stream_h2c_ctrl_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_stream_en(self):
        """perf. counter enable"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_POS) & self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_MSK

    @perf_stream_en.setter
    def perf_stream_en(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_MSK << self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_MSK) << self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_ADDR, rdata)

    @property
    def perf_stream_clear(self):
        """perf. counter clear"""
        return 0

    @perf_stream_clear.setter
    def perf_stream_clear(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_MSK << self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_MSK) << self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_ADDR, rdata)


class _RegCnn_accel_perf_stream_h2c_lh_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_stream_lh(self):
        """perf. counter value"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_STREAM_H2C_LH_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_POS) & self._rmap.CNN_ACCEL_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_MSK


class _RegCnn_accel_perf_stream_h2c_uh_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_stream_uh(self):
        """perf. counter value"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_STREAM_H2C_UH_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_POS) & self._rmap.CNN_ACCEL_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_MSK


class _RegCnn_accel_perf_cache_stall_ctrl_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_stream_en(self):
        """perf. counter enable"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_POS) & self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_MSK

    @perf_stream_en.setter
    def perf_stream_en(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_MSK << self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_MSK) << self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_ADDR, rdata)

    @property
    def perf_stream_clear(self):
        """perf. counter clear"""
        return 0

    @perf_stream_clear.setter
    def perf_stream_clear(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_MSK << self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_MSK) << self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_ADDR, rdata)


class _RegCnn_accel_perf_cache_stall_lh_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_stream_lh(self):
        """perf. counter value"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_CACHE_STALL_LH_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_POS) & self._rmap.CNN_ACCEL_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_MSK


class _RegCnn_accel_perf_cache_stall_uh_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def perf_stream_uh(self):
        """perf. counter value"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_PERF_CACHE_STALL_UH_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_POS) & self._rmap.CNN_ACCEL_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_MSK


class _RegCnn_accel_tens_trans_cfg_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_trans_type(self):
        """tensor trans. type"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_MSK

    @tens_trans_type.setter
    def tens_trans_type(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR, rdata)

    @property
    def nlin_f_type(self):
        """nonlin. function type"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_MSK

    @nlin_f_type.setter
    def nlin_f_type(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR, rdata)

    @property
    def batch_norm_en(self):
        """batch normalization enable"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_MSK

    @batch_norm_en.setter
    def batch_norm_en(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR, rdata)

    @property
    def repl_bias(self):
        """replicate bias flag"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_MSK

    @repl_bias.setter
    def repl_bias(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR, rdata)

    @property
    def bias_en(self):
        """bias enable"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_MSK

    @bias_en.setter
    def bias_en(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR, rdata)

class _RegCnn_accel_tens_trans_conv_cfg_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def conv_stride_0(self):
        """convolution stride"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_MSK

    @conv_stride_0.setter
    def conv_stride_0(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR, rdata)

    @property
    def conv_stride_1(self):
        """convolution stride"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_MSK

    @conv_stride_1.setter
    def conv_stride_1(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR, rdata)

    @property
    def conv_padding_0(self):
        """convolution zero padding"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_MSK

    @conv_padding_0.setter
    def conv_padding_0(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR, rdata)

    @property
    def conv_padding_1(self):
        """convolution zero padding"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_MSK

    @conv_padding_1.setter
    def conv_padding_1(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_addr_src_a_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_addr(self):
        """tensor address"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_MSK

    @tens_addr.setter
    def tens_addr(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_addr_src_b_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_addr(self):
        """tensor address"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_MSK

    @tens_addr.setter
    def tens_addr(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_addr_batch_norm_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_addr(self):
        """tensor address"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_MSK

    @tens_addr.setter
    def tens_addr(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_addr_bias_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_addr(self):
        """tensor address"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_MSK

    @tens_addr.setter
    def tens_addr(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_addr_res_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_addr(self):
        """tensor address"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_MSK

    @tens_addr.setter
    def tens_addr(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_lin_dims_src_a_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_0_dim(self):
        """row size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_MSK

    @tens_0_dim.setter
    def tens_0_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR, rdata)

    @property
    def tens_1_dim(self):
        """column size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_MSK

    @tens_1_dim.setter
    def tens_1_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_lin_dims_src_b_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_0_dim(self):
        """row size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_MSK

    @tens_0_dim.setter
    def tens_0_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR, rdata)

    @property
    def tens_1_dim(self):
        """column size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_MSK

    @tens_1_dim.setter
    def tens_1_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_lin_dims_res_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_0_dim(self):
        """row size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_MSK

    @tens_0_dim.setter
    def tens_0_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR, rdata)

    @property
    def tens_1_dim(self):
        """column size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_MSK

    @tens_1_dim.setter
    def tens_1_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_conv_dims_src_a_0_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_0_dim(self):
        """row size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_MSK

    @tens_0_dim.setter
    def tens_0_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR, rdata)

    @property
    def tens_1_dim(self):
        """column size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_MSK

    @tens_1_dim.setter
    def tens_1_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_conv_dims_src_a_1_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_2_dim(self):
        """row size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_MSK

    @tens_2_dim.setter
    def tens_2_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR, rdata)

    @property
    def tens_3_dim(self):
        """column size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_MSK

    @tens_3_dim.setter
    def tens_3_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_conv_dims_src_b_0_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_0_dim(self):
        """row size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_MSK

    @tens_0_dim.setter
    def tens_0_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR, rdata)

    @property
    def tens_1_dim(self):
        """column size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_MSK

    @tens_1_dim.setter
    def tens_1_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_conv_dims_src_b_1_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_2_dim(self):
        """row size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_MSK

    @tens_2_dim.setter
    def tens_2_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR, rdata)

    @property
    def tens_3_dim(self):
        """column size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_MSK

    @tens_3_dim.setter
    def tens_3_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_conv_dims_res_0_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_0_dim(self):
        """row size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_MSK

    @tens_0_dim.setter
    def tens_0_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR, rdata)

    @property
    def tens_1_dim(self):
        """column size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_MSK

    @tens_1_dim.setter
    def tens_1_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR, rdata)


class _RegCnn_accel_tens_trans_conv_dims_res_1_reg:
    def __init__(self, rmap):
        self._rmap = rmap

    @property
    def tens_2_dim(self):
        """row size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_MSK

    @tens_2_dim.setter
    def tens_2_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR, rdata)

    @property
    def tens_3_dim(self):
        """column size"""
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR)
        return (rdata >> self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_POS) & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_MSK

    @tens_3_dim.setter
    def tens_3_dim(self, val):
        rdata = self._rmap._if.read(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR)
        rdata = rdata & (~(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_MSK << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_POS))
        rdata = rdata | ((val & self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_MSK) << self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_POS)
        self._rmap._if.write(self._rmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR, rdata)


class RegMap:
    """Control/Status register map"""

    # CNN_ACCEL_CTRL_REG - main control register
    CNN_ACCEL_CTRL_REG_ADDR = 0x00000000
    CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_START_POS = 0
    CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_START_MSK = 0x1
    CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_POS = 1
    CNN_ACCEL_CTRL_REG_TENS_TRANS_SEQ_LEN_MSK = 0x3ff
    CNN_ACCEL_CTRL_REG_SOFT_RESET_POS = 11
    CNN_ACCEL_CTRL_REG_SOFT_RESET_MSK = 0x1

    # CNN_ACCEL_STAT_REG - main status register
    CNN_ACCEL_STAT_REG_ADDR = 0x00000004
    CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_BUSY_POS = 0
    CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_BUSY_MSK = 0x1
    CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_CNT_POS = 1
    CNN_ACCEL_STAT_REG_TENS_TRANS_SEQ_CNT_MSK = 0x3ff

    # CNN_ACCEL_INT_REG - main interrupt register
    CNN_ACCEL_INT_REG_ADDR = 0x00000008
    CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_POS = 0
    CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_EN_MSK = 0x1
    CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_POS = 1
    CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_STAT_MSK = 0x1
    CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_POS = 2
    CNN_ACCEL_INT_REG_INT_TENS_TRANS_SEQ_DONE_CLEAR_MSK = 0x1
    CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_POS = 3
    CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_EN_MSK = 0x1
    CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_STAT_POS = 4
    CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_STAT_MSK = 0x1
    CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_CLEAR_POS = 5
    CNN_ACCEL_INT_REG_INT_STREAM_H2C_DONE_CLEAR_MSK = 0x1
    CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_POS = 6
    CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_EN_MSK = 0x1
    CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_STAT_POS = 7
    CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_STAT_MSK = 0x1
    CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_CLEAR_POS = 8
    CNN_ACCEL_INT_REG_INT_STREAM_C2H_DONE_CLEAR_MSK = 0x1

    # CNN_ACCEL_MMEM_OFFSET_REG - address offset for the main memory access
    CNN_ACCEL_MMEM_OFFSET_REG_ADDR = 0x0000000c
    CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_POS = 0
    CNN_ACCEL_MMEM_OFFSET_REG_MMEM_BASE_ADDR_MSK = 0xffffffff

    # CNN_ACCEL_GP_RW_REG - general purpose read-write register
    CNN_ACCEL_GP_RW_REG_ADDR = 0x00000010
    CNN_ACCEL_GP_RW_REG_GP_RW_POS = 0
    CNN_ACCEL_GP_RW_REG_GP_RW_MSK = 0xffffffff

    # CNN_ACCEL_PERF_RUN_CTRL_REG - performance counter - run cycles - control register
    CNN_ACCEL_PERF_RUN_CTRL_REG_ADDR = 0x00000014
    CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_POS = 0
    CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_EN_MSK = 0x1
    CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_POS = 1
    CNN_ACCEL_PERF_RUN_CTRL_REG_PERF_RUN_CLEAR_MSK = 0x1

    # CNN_ACCEL_PERF_RUN_LH_REG - performance counter - run cycles - lower half
    CNN_ACCEL_PERF_RUN_LH_REG_ADDR = 0x00000018
    CNN_ACCEL_PERF_RUN_LH_REG_PERF_RUN_LH_POS = 0
    CNN_ACCEL_PERF_RUN_LH_REG_PERF_RUN_LH_MSK = 0xffffffff

    # CNN_ACCEL_PERF_RUN_UH_REG - performance counter - run cycles - upper half
    CNN_ACCEL_PERF_RUN_UH_REG_ADDR = 0x0000001c
    CNN_ACCEL_PERF_RUN_UH_REG_PERF_RUN_UH_POS = 0
    CNN_ACCEL_PERF_RUN_UH_REG_PERF_RUN_UH_MSK = 0xffffffff

    # CNN_ACCEL_PERF_COMP_CTRL_REG - performance counter - computation cycles - control register
    CNN_ACCEL_PERF_COMP_CTRL_REG_ADDR = 0x00000020
    CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_POS = 0
    CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_EN_MSK = 0x1
    CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_POS = 1
    CNN_ACCEL_PERF_COMP_CTRL_REG_PERF_COMP_CLEAR_MSK = 0x1

    # CNN_ACCEL_PERF_COMP_LH_REG - performance counter - run cycles - lower half
    CNN_ACCEL_PERF_COMP_LH_REG_ADDR = 0x00000024
    CNN_ACCEL_PERF_COMP_LH_REG_PERF_COMP_LH_POS = 0
    CNN_ACCEL_PERF_COMP_LH_REG_PERF_COMP_LH_MSK = 0xffffffff

    # CNN_ACCEL_PERF_COMP_UH_REG - performance counter - run cycles - upper half
    CNN_ACCEL_PERF_COMP_UH_REG_ADDR = 0x00000028
    CNN_ACCEL_PERF_COMP_UH_REG_PERF_COMP_UH_POS = 0
    CNN_ACCEL_PERF_COMP_UH_REG_PERF_COMP_UH_MSK = 0xffffffff

    # CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG - performance counter - stream C2H cycles - control register
    CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_ADDR = 0x0000002c
    CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_POS = 0
    CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_EN_MSK = 0x1
    CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_POS = 1
    CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_PERF_STREAM_CLEAR_MSK = 0x1

    # CNN_ACCEL_PERF_STREAM_C2H_LH_REG - performance counter - run cycles - lower half
    CNN_ACCEL_PERF_STREAM_C2H_LH_REG_ADDR = 0x00000030
    CNN_ACCEL_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_POS = 0
    CNN_ACCEL_PERF_STREAM_C2H_LH_REG_PERF_STREAM_LH_MSK = 0xffffffff

    # CNN_ACCEL_PERF_STREAM_C2H_UH_REG - performance counter - run cycles - upper half
    CNN_ACCEL_PERF_STREAM_C2H_UH_REG_ADDR = 0x00000034
    CNN_ACCEL_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_POS = 0
    CNN_ACCEL_PERF_STREAM_C2H_UH_REG_PERF_STREAM_UH_MSK = 0xffffffff

    # CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG - performance counter - stream H2C cycles - control register
    CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_ADDR = 0x00000038
    CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_POS = 0
    CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_EN_MSK = 0x1
    CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_POS = 1
    CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_PERF_STREAM_CLEAR_MSK = 0x1

    # CNN_ACCEL_PERF_STREAM_H2C_LH_REG - performance counter - run cycles - lower half
    CNN_ACCEL_PERF_STREAM_H2C_LH_REG_ADDR = 0x0000003c
    CNN_ACCEL_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_POS = 0
    CNN_ACCEL_PERF_STREAM_H2C_LH_REG_PERF_STREAM_LH_MSK = 0xffffffff

    # CNN_ACCEL_PERF_STREAM_H2C_UH_REG - performance counter - run cycles - upper half
    CNN_ACCEL_PERF_STREAM_H2C_UH_REG_ADDR = 0x00000040
    CNN_ACCEL_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_POS = 0
    CNN_ACCEL_PERF_STREAM_H2C_UH_REG_PERF_STREAM_UH_MSK = 0xffffffff

    # CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG - performance counter - cache stall - control register
    CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_ADDR = 0x00000044
    CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_POS = 0
    CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_EN_MSK = 0x1
    CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_POS = 1
    CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_PERF_STREAM_CLEAR_MSK = 0x1

    # CNN_ACCEL_PERF_CACHE_STALL_LH_REG - performance counter - run cycles - lower half
    CNN_ACCEL_PERF_CACHE_STALL_LH_REG_ADDR = 0x00000048
    CNN_ACCEL_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_POS = 0
    CNN_ACCEL_PERF_CACHE_STALL_LH_REG_PERF_STREAM_LH_MSK = 0xffffffff

    # CNN_ACCEL_PERF_CACHE_STALL_UH_REG - performance counter - run cycles - upper half
    CNN_ACCEL_PERF_CACHE_STALL_UH_REG_ADDR = 0x0000004c
    CNN_ACCEL_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_POS = 0
    CNN_ACCEL_PERF_CACHE_STALL_UH_REG_PERF_STREAM_UH_MSK = 0xffffffff

    # CNN_ACCEL_TENS_TRANS_CFG_REG - tensor trans. configuration
    CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR = 0x00000050
    CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_POS = 0
    CNN_ACCEL_TENS_TRANS_CFG_REG_TENS_TRANS_TYPE_MSK = 0xf
    CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_POS = 4
    CNN_ACCEL_TENS_TRANS_CFG_REG_NLIN_F_TYPE_MSK = 0xf
    CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_POS = 8
    CNN_ACCEL_TENS_TRANS_CFG_REG_BATCH_NORM_EN_MSK = 0x1
    CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_POS = 9
    CNN_ACCEL_TENS_TRANS_CFG_REG_REPL_BIAS_MSK = 0x1
    CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_POS = 10
    CNN_ACCEL_TENS_TRANS_CFG_REG_BIAS_EN_MSK = 0x1

    # CNN_ACCEL_TENS_TRANS_CONV_CFG_REG - convolution configuration
    CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR = 0x00000054
    CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_POS = 0
    CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_0_MSK = 0xff
    CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_POS = 8
    CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_STRIDE_1_MSK = 0xff
    CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_POS = 16
    CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_0_MSK = 0xff
    CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_POS = 24
    CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_CONV_PADDING_1_MSK = 0xff

    # CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG - tensor start address
    CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_ADDR = 0x00000058
    CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_POS = 0
    CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_TENS_ADDR_MSK = 0xffffffff

    # CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG - tensor start address
    CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_ADDR = 0x0000005c
    CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_POS = 0
    CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_TENS_ADDR_MSK = 0xffffffff

    # CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG - tensor start address
    CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_ADDR = 0x00000060
    CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_POS = 0
    CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_TENS_ADDR_MSK = 0xffffffff

    # CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG - tensor start address
    CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_ADDR = 0x00000064
    CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_POS = 0
    CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_TENS_ADDR_MSK = 0xffffffff

    # CNN_ACCEL_TENS_TRANS_ADDR_RES_REG - tensor start address
    CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_ADDR = 0x00000068
    CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_POS = 0
    CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_TENS_ADDR_MSK = 0xffffffff

    # CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG - tensor trans. linear (matrix) dimensions
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR = 0x0000006c
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_POS = 0
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_0_DIM_MSK = 0xffff
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_POS = 16
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_TENS_1_DIM_MSK = 0xffff

    # CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG - tensor trans. linear (matrix) dimensions
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR = 0x00000070
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_POS = 0
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_0_DIM_MSK = 0xffff
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_POS = 16
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_TENS_1_DIM_MSK = 0xffff

    # CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG - tensor trans. linear (matrix) dimensions
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR = 0x00000074
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_POS = 0
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_0_DIM_MSK = 0xffff
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_POS = 16
    CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_TENS_1_DIM_MSK = 0xffff

    # CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG - tensor trans. convolution dimensions
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR = 0x00000078
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_POS = 0
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_0_DIM_MSK = 0xffff
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_POS = 16
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_TENS_1_DIM_MSK = 0xffff

    # CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG - tensor trans. convolution dimensions
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR = 0x0000007c
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_POS = 0
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_2_DIM_MSK = 0xffff
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_POS = 16
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_TENS_3_DIM_MSK = 0xffff

    # CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG - tensor trans. convolution dimensions
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR = 0x00000080
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_POS = 0
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_0_DIM_MSK = 0xffff
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_POS = 16
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_TENS_1_DIM_MSK = 0xffff

    # CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG - tensor trans. convolution dimensions
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR = 0x00000084
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_POS = 0
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_2_DIM_MSK = 0xffff
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_POS = 16
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_TENS_3_DIM_MSK = 0xffff

    # CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG - tensor trans. convolution dimensions
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR = 0x00000088
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_POS = 0
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_0_DIM_MSK = 0xffff
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_POS = 16
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_TENS_1_DIM_MSK = 0xffff

    # CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG - tensor trans. convolution dimensions
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR = 0x0000008c
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_POS = 0
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_2_DIM_MSK = 0xffff
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_POS = 16
    CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_TENS_3_DIM_MSK = 0xffff

    def __init__(self, interface):
        self._if = interface

    @property
    def cnn_accel_ctrl_reg(self):
        """main control register"""
        return self._if.read(self.CNN_ACCEL_CTRL_REG_ADDR)

    @cnn_accel_ctrl_reg.setter
    def cnn_accel_ctrl_reg(self, val):
        self._if.write(self.CNN_ACCEL_CTRL_REG_ADDR, val)

    @property
    def cnn_accel_ctrl_reg_bf(self):
        return _RegCnn_accel_ctrl_reg(self)

    @property
    def cnn_accel_stat_reg(self):
        """main status register"""
        return self._if.read(self.CNN_ACCEL_STAT_REG_ADDR)

    @property
    def cnn_accel_stat_reg_bf(self):
        return _RegCnn_accel_stat_reg(self)

    @property
    def cnn_accel_int_reg(self):
        """main interrupt register"""
        return self._if.read(self.CNN_ACCEL_INT_REG_ADDR)

    @cnn_accel_int_reg.setter
    def cnn_accel_int_reg(self, val):
        self._if.write(self.CNN_ACCEL_INT_REG_ADDR, val)

    @property
    def cnn_accel_int_reg_bf(self):
        return _RegCnn_accel_int_reg(self)

    @property
    def cnn_accel_mmem_offset_reg(self):
        """address offset for the main memory access"""
        return self._if.read(self.CNN_ACCEL_MMEM_OFFSET_REG_ADDR)

    @cnn_accel_mmem_offset_reg.setter
    def cnn_accel_mmem_offset_reg(self, val):
        self._if.write(self.CNN_ACCEL_MMEM_OFFSET_REG_ADDR, val)

    @property
    def cnn_accel_mmem_offset_reg_bf(self):
        return _RegCnn_accel_mmem_offset_reg(self)

    @property
    def cnn_accel_gp_rw_reg(self):
        """general purpose read-write register"""
        return self._if.read(self.CNN_ACCEL_GP_RW_REG_ADDR)

    @cnn_accel_gp_rw_reg.setter
    def cnn_accel_gp_rw_reg(self, val):
        self._if.write(self.CNN_ACCEL_GP_RW_REG_ADDR, val)

    @property
    def cnn_accel_gp_rw_reg_bf(self):
        return _RegCnn_accel_gp_rw_reg(self)

    @property
    def cnn_accel_perf_run_ctrl_reg(self):
        """performance counter - run cycles - control register"""
        return self._if.read(self.CNN_ACCEL_PERF_RUN_CTRL_REG_ADDR)

    @cnn_accel_perf_run_ctrl_reg.setter
    def cnn_accel_perf_run_ctrl_reg(self, val):
        self._if.write(self.CNN_ACCEL_PERF_RUN_CTRL_REG_ADDR, val)

    @property
    def cnn_accel_perf_run_ctrl_reg_bf(self):
        return _RegCnn_accel_perf_run_ctrl_reg(self)

    @property
    def cnn_accel_perf_run_lh_reg(self):
        """performance counter - run cycles - lower half"""
        return self._if.read(self.CNN_ACCEL_PERF_RUN_LH_REG_ADDR)

    @property
    def cnn_accel_perf_run_lh_reg_bf(self):
        return _RegCnn_accel_perf_run_lh_reg(self)

    @property
    def cnn_accel_perf_run_uh_reg(self):
        """performance counter - run cycles - upper half"""
        return self._if.read(self.CNN_ACCEL_PERF_RUN_UH_REG_ADDR)

    @property
    def cnn_accel_perf_run_uh_reg_bf(self):
        return _RegCnn_accel_perf_run_uh_reg(self)

    @property
    def cnn_accel_perf_comp_ctrl_reg(self):
        """performance counter - computation cycles - control register"""
        return self._if.read(self.CNN_ACCEL_PERF_COMP_CTRL_REG_ADDR)

    @cnn_accel_perf_comp_ctrl_reg.setter
    def cnn_accel_perf_comp_ctrl_reg(self, val):
        self._if.write(self.CNN_ACCEL_PERF_COMP_CTRL_REG_ADDR, val)

    @property
    def cnn_accel_perf_comp_ctrl_reg_bf(self):
        return _RegCnn_accel_perf_comp_ctrl_reg(self)

    @property
    def cnn_accel_perf_comp_lh_reg(self):
        """performance counter - run cycles - lower half"""
        return self._if.read(self.CNN_ACCEL_PERF_COMP_LH_REG_ADDR)

    @property
    def cnn_accel_perf_comp_lh_reg_bf(self):
        return _RegCnn_accel_perf_comp_lh_reg(self)

    @property
    def cnn_accel_perf_comp_uh_reg(self):
        """performance counter - run cycles - upper half"""
        return self._if.read(self.CNN_ACCEL_PERF_COMP_UH_REG_ADDR)

    @property
    def cnn_accel_perf_comp_uh_reg_bf(self):
        return _RegCnn_accel_perf_comp_uh_reg(self)

    @property
    def cnn_accel_perf_stream_c2h_ctrl_reg(self):
        """performance counter - stream C2H cycles - control register"""
        return self._if.read(self.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_ADDR)

    @cnn_accel_perf_stream_c2h_ctrl_reg.setter
    def cnn_accel_perf_stream_c2h_ctrl_reg(self, val):
        self._if.write(self.CNN_ACCEL_PERF_STREAM_C2H_CTRL_REG_ADDR, val)

    @property
    def cnn_accel_perf_stream_c2h_ctrl_reg_bf(self):
        return _RegCnn_accel_perf_stream_c2h_ctrl_reg(self)

    @property
    def cnn_accel_perf_stream_c2h_lh_reg(self):
        """performance counter - run cycles - lower half"""
        return self._if.read(self.CNN_ACCEL_PERF_STREAM_C2H_LH_REG_ADDR)

    @property
    def cnn_accel_perf_stream_c2h_lh_reg_bf(self):
        return _RegCnn_accel_perf_stream_c2h_lh_reg(self)

    @property
    def cnn_accel_perf_stream_c2h_uh_reg(self):
        """performance counter - run cycles - upper half"""
        return self._if.read(self.CNN_ACCEL_PERF_STREAM_C2H_UH_REG_ADDR)

    @property
    def cnn_accel_perf_stream_c2h_uh_reg_bf(self):
        return _RegCnn_accel_perf_stream_c2h_uh_reg(self)

    @property
    def cnn_accel_perf_stream_h2c_ctrl_reg(self):
        """performance counter - stream H2C cycles - control register"""
        return self._if.read(self.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_ADDR)

    @cnn_accel_perf_stream_h2c_ctrl_reg.setter
    def cnn_accel_perf_stream_h2c_ctrl_reg(self, val):
        self._if.write(self.CNN_ACCEL_PERF_STREAM_H2C_CTRL_REG_ADDR, val)

    @property
    def cnn_accel_perf_stream_h2c_ctrl_reg_bf(self):
        return _RegCnn_accel_perf_stream_h2c_ctrl_reg(self)

    @property
    def cnn_accel_perf_stream_h2c_lh_reg(self):
        """performance counter - run cycles - lower half"""
        return self._if.read(self.CNN_ACCEL_PERF_STREAM_H2C_LH_REG_ADDR)

    @property
    def cnn_accel_perf_stream_h2c_lh_reg_bf(self):
        return _RegCnn_accel_perf_stream_h2c_lh_reg(self)

    @property
    def cnn_accel_perf_stream_h2c_uh_reg(self):
        """performance counter - run cycles - upper half"""
        return self._if.read(self.CNN_ACCEL_PERF_STREAM_H2C_UH_REG_ADDR)

    @property
    def cnn_accel_perf_stream_h2c_uh_reg_bf(self):
        return _RegCnn_accel_perf_stream_h2c_uh_reg(self)

    @property
    def cnn_accel_perf_cache_stall_ctrl_reg(self):
        """performance counter - cache stall - control register"""
        return self._if.read(self.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_ADDR)

    @cnn_accel_perf_cache_stall_ctrl_reg.setter
    def cnn_accel_perf_cache_stall_ctrl_reg(self, val):
        self._if.write(self.CNN_ACCEL_PERF_CACHE_STALL_CTRL_REG_ADDR, val)

    @property
    def cnn_accel_perf_cache_stall_ctrl_reg_bf(self):
        return _RegCnn_accel_perf_cache_stall_ctrl_reg(self)

    @property
    def cnn_accel_perf_cache_stall_lh_reg(self):
        """performance counter - run cycles - lower half"""
        return self._if.read(self.CNN_ACCEL_PERF_CACHE_STALL_LH_REG_ADDR)

    @property
    def cnn_accel_perf_cache_stall_lh_reg_bf(self):
        return _RegCnn_accel_perf_cache_stall_lh_reg(self)

    @property
    def cnn_accel_perf_cache_stall_uh_reg(self):
        """performance counter - run cycles - upper half"""
        return self._if.read(self.CNN_ACCEL_PERF_CACHE_STALL_UH_REG_ADDR)

    @property
    def cnn_accel_perf_cache_stall_uh_reg_bf(self):
        return _RegCnn_accel_perf_cache_stall_uh_reg(self)

    @property
    def cnn_accel_tens_trans_cfg_reg(self):
        """tensor trans. configuration"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR)

    @cnn_accel_tens_trans_cfg_reg.setter
    def cnn_accel_tens_trans_cfg_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_cfg_reg_bf(self):
        return _RegCnn_accel_tens_trans_cfg_reg(self)

    @property
    def cnn_accel_tens_trans_conv_cfg_reg(self):
        """convolution configuration"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR)

    @cnn_accel_tens_trans_conv_cfg_reg.setter
    def cnn_accel_tens_trans_conv_cfg_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_CONV_CFG_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_conv_cfg_reg_bf(self):
        return _RegCnn_accel_tens_trans_conv_cfg_reg(self)

    @property
    def cnn_accel_tens_trans_addr_src_a_reg(self):
        """tensor start address"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_ADDR)

    @cnn_accel_tens_trans_addr_src_a_reg.setter
    def cnn_accel_tens_trans_addr_src_a_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_ADDR_SRC_A_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_addr_src_a_reg_bf(self):
        return _RegCnn_accel_tens_trans_addr_src_a_reg(self)

    @property
    def cnn_accel_tens_trans_addr_src_b_reg(self):
        """tensor start address"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_ADDR)

    @cnn_accel_tens_trans_addr_src_b_reg.setter
    def cnn_accel_tens_trans_addr_src_b_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_ADDR_SRC_B_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_addr_src_b_reg_bf(self):
        return _RegCnn_accel_tens_trans_addr_src_b_reg(self)

    @property
    def cnn_accel_tens_trans_addr_batch_norm_reg(self):
        """tensor start address"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_ADDR)

    @cnn_accel_tens_trans_addr_batch_norm_reg.setter
    def cnn_accel_tens_trans_addr_batch_norm_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_ADDR_BATCH_NORM_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_addr_batch_norm_reg_bf(self):
        return _RegCnn_accel_tens_trans_addr_batch_norm_reg(self)

    @property
    def cnn_accel_tens_trans_addr_bias_reg(self):
        """tensor start address"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_ADDR)

    @cnn_accel_tens_trans_addr_bias_reg.setter
    def cnn_accel_tens_trans_addr_bias_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_ADDR_BIAS_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_addr_bias_reg_bf(self):
        return _RegCnn_accel_tens_trans_addr_bias_reg(self)

    @property
    def cnn_accel_tens_trans_addr_res_reg(self):
        """tensor start address"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_ADDR)

    @cnn_accel_tens_trans_addr_res_reg.setter
    def cnn_accel_tens_trans_addr_res_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_ADDR_RES_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_addr_res_reg_bf(self):
        return _RegCnn_accel_tens_trans_addr_res_reg(self)

    @property
    def cnn_accel_tens_trans_lin_dims_src_a_reg(self):
        """tensor trans. linear (matrix) dimensions"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR)

    @cnn_accel_tens_trans_lin_dims_src_a_reg.setter
    def cnn_accel_tens_trans_lin_dims_src_a_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_A_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_lin_dims_src_a_reg_bf(self):
        return _RegCnn_accel_tens_trans_lin_dims_src_a_reg(self)

    @property
    def cnn_accel_tens_trans_lin_dims_src_b_reg(self):
        """tensor trans. linear (matrix) dimensions"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR)

    @cnn_accel_tens_trans_lin_dims_src_b_reg.setter
    def cnn_accel_tens_trans_lin_dims_src_b_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_LIN_DIMS_SRC_B_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_lin_dims_src_b_reg_bf(self):
        return _RegCnn_accel_tens_trans_lin_dims_src_b_reg(self)

    @property
    def cnn_accel_tens_trans_lin_dims_res_reg(self):
        """tensor trans. linear (matrix) dimensions"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR)

    @cnn_accel_tens_trans_lin_dims_res_reg.setter
    def cnn_accel_tens_trans_lin_dims_res_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_lin_dims_res_reg_bf(self):
        return _RegCnn_accel_tens_trans_lin_dims_res_reg(self)

    @property
    def cnn_accel_tens_trans_conv_dims_src_a_0_reg(self):
        """tensor trans. convolution dimensions"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR)

    @cnn_accel_tens_trans_conv_dims_src_a_0_reg.setter
    def cnn_accel_tens_trans_conv_dims_src_a_0_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_0_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_conv_dims_src_a_0_reg_bf(self):
        return _RegCnn_accel_tens_trans_conv_dims_src_a_0_reg(self)

    @property
    def cnn_accel_tens_trans_conv_dims_src_a_1_reg(self):
        """tensor trans. convolution dimensions"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR)

    @cnn_accel_tens_trans_conv_dims_src_a_1_reg.setter
    def cnn_accel_tens_trans_conv_dims_src_a_1_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_A_1_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_conv_dims_src_a_1_reg_bf(self):
        return _RegCnn_accel_tens_trans_conv_dims_src_a_1_reg(self)

    @property
    def cnn_accel_tens_trans_conv_dims_src_b_0_reg(self):
        """tensor trans. convolution dimensions"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR)

    @cnn_accel_tens_trans_conv_dims_src_b_0_reg.setter
    def cnn_accel_tens_trans_conv_dims_src_b_0_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_0_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_conv_dims_src_b_0_reg_bf(self):
        return _RegCnn_accel_tens_trans_conv_dims_src_b_0_reg(self)

    @property
    def cnn_accel_tens_trans_conv_dims_src_b_1_reg(self):
        """tensor trans. convolution dimensions"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR)

    @cnn_accel_tens_trans_conv_dims_src_b_1_reg.setter
    def cnn_accel_tens_trans_conv_dims_src_b_1_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_SRC_B_1_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_conv_dims_src_b_1_reg_bf(self):
        return _RegCnn_accel_tens_trans_conv_dims_src_b_1_reg(self)

    @property
    def cnn_accel_tens_trans_conv_dims_res_0_reg(self):
        """tensor trans. convolution dimensions"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR)

    @cnn_accel_tens_trans_conv_dims_res_0_reg.setter
    def cnn_accel_tens_trans_conv_dims_res_0_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_0_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_conv_dims_res_0_reg_bf(self):
        return _RegCnn_accel_tens_trans_conv_dims_res_0_reg(self)

    @property
    def cnn_accel_tens_trans_conv_dims_res_1_reg(self):
        """tensor trans. convolution dimensions"""
        return self._if.read(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR)

    @cnn_accel_tens_trans_conv_dims_res_1_reg.setter
    def cnn_accel_tens_trans_conv_dims_res_1_reg(self, val):
        self._if.write(self.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR, val)

    @property
    def cnn_accel_tens_trans_conv_dims_res_1_reg_bf(self):
        return _RegCnn_accel_tens_trans_conv_dims_res_1_reg(self)