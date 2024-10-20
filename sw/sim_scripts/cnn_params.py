#!/usr/bin/python3
"""
Author: Martin Lastovka, @RWTH DSP 
Project: Efficient FPGA CNN implementation for 5G physical layer - Master Thesis @ RWTH DSP
Desc: All the shared constants and classes descriptions for the supporting python scripts
"""

from enum import IntEnum
from typing import NamedTuple
from fxpmath import Fxp as fxp

C_CONV_PARAM_WDT         = 8
C_TENS_DIM_WDT           = 16
C_MMEM_ADDR_WDT          = 32
C_VECT_SIZE              = 5
C_MMEM_SIZE              = 2**13
C_REGMAP_ADDR_WDT        = 16
C_ARITH_TYPE             = "FIXED_POINT"
C_ARITH_FXP_INT_WDT      = 8
C_ARITH_FXP_FRAC_WDT     = 10
C_ARITH_FXP_WORD_WDT     = C_ARITH_FXP_INT_WDT + C_ARITH_FXP_FRAC_WDT
C_ARITH_FXP_EXT_INT_WDT  = 8
C_ARITH_FXP_EXT_FRAC_WDT = 8
C_ARITH_FXP_EXT_WORD_WDT = C_ARITH_FXP_EXT_INT_WDT + C_ARITH_FXP_EXT_FRAC_WDT
C_ARITH_FXP_EXT_BYTE_LEN = C_ARITH_FXP_EXT_WORD_WDT // 8
C_ARITH_FXP_ULP          = 2.0**(-C_ARITH_FXP_FRAC_WDT)
C_ARITH_SATUR            = True
C_MAX_REL_ERR            = 0.05
C_EPS                    = 0.00001
C_TANH_DOWN_SA_FACT      = 8
C_TANH_LIN_END           = 0.25
C_TANH_SAT_START         = 4.2
C_TANH_LUT_MEM           = None #initialized by gen_tanh_lut.py

FXP_INT_WORD        = fxp(None, signed=True, n_word=C_ARITH_FXP_WORD_WDT, n_frac=C_ARITH_FXP_FRAC_WDT, rounding='floor') #template for the data word
FXP_INT_WORD.config.const_op_sizing = 'same'
FXP_INT_WORD.config.op_sizing       = 'same'

FXP_EXT_WORD        = fxp(None, signed=True, n_word=C_ARITH_FXP_EXT_WORD_WDT, n_frac=C_ARITH_FXP_EXT_FRAC_WDT, rounding='floor') #template for the data word
FXP_EXT_WORD.config.const_op_sizing = 'same'
FXP_EXT_WORD.config.op_sizing       = 'same'

class layout_t(IntEnum):
    ROW_FIRST = 0
    COL_FIRST = 1

class tens_trans_type_t(IntEnum):
    TRANS_LIN = 0        
    TRANS_CONV = 1
    TRANS_MAXPOOL = 2
    TRANS_STREAM = 3

class nlin_f_type_t(IntEnum):
    NLIN_F_IDENTITY = 0,        
    NLIN_F_RELU = 1,
    NLIN_F_TANH = 2

class conv_cfg_t(NamedTuple):
    conv_stride_0:  int
    conv_stride_1:  int
    conv_padding_0: int
    conv_padding_1: int

class tens_trans_dim_t(NamedTuple):
    tens_0_dim: int
    tens_1_dim: int
    tens_2_dim: int
    tens_3_dim: int

class mtx_trans_dim_t(NamedTuple):
    tens_0_dim: tens_trans_dim_t
    tens_1_dim: tens_trans_dim_t

class mtx_trans_dims_t(NamedTuple):
    tens_src_a_dims: mtx_trans_dim_t
    tens_src_b_dims: mtx_trans_dim_t
    tens_res_dims:   mtx_trans_dim_t

class tens_trans_dims_t(NamedTuple):
    tens_src_a_dims: tens_trans_dim_t
    tens_src_b_dims: tens_trans_dim_t
    tens_res_dims:   tens_trans_dim_t

class tens_trans_addrs_t(NamedTuple):
    tens_src_a_addr:        int
    tens_src_b_addr:        int
    tens_batch_norm_addr:   int
    tens_bias_addr:         int
    tens_res_addr:          int

class tens_trans_spec_t:
    def __init__(self):
        self._tens_trans_type   = tens_trans_type_t.TRANS_LIN
        self._nlin_f_type       = nlin_f_type_t.NLIN_F_IDENTITY
        self._batch_norm_en     = False
        self._bias_en           = False
        self._repl_bias         = False
        self._conv_cfg          = conv_cfg_t(conv_stride_0=0, conv_stride_1=0, conv_padding_0=0, conv_padding_1=0)
        self._tens_trans_dims   = tens_trans_dims_t(tens_src_a_dims=tens_trans_dim_t(0, 0, 0, 0), tens_src_b_dims=tens_trans_dim_t(0, 0, 0, 0), tens_res_dims=tens_trans_dim_t(0, 0, 0, 0))
        self._mtx_trans_dims    = mtx_trans_dims_t(tens_src_a_dims=mtx_trans_dim_t(0, 0), tens_src_b_dims=mtx_trans_dim_t(0, 0), tens_res_dims=mtx_trans_dim_t(0, 0))
        self._tens_trans_addrs  = tens_trans_addrs_t(tens_src_a_addr=0, tens_src_b_addr=0, tens_batch_norm_addr=0, tens_bias_addr=0, tens_res_addr=0)

    @property
    def tens_trans_type(self):
        return self._tens_trans_type

    @tens_trans_type.setter
    def tens_trans_type(self, val):
        assert isinstance(val, tens_trans_type_t), "Error: incorrect type, expecting enum"
        self._tens_trans_type = val

    @property
    def nlin_f_type(self):
        return self._nlin_f_type

    @nlin_f_type.setter
    def nlin_f_type(self, val):
        assert isinstance(val, nlin_f_type_t), "Error: incorrect type, expecting enum"
        self._nlin_f_type = val

    @property
    def conv_cfg(self):
        return self._conv_cfg

    @conv_cfg.setter
    def conv_cfg(self, val):
        assert isinstance(val, conv_cfg_t), "Error: incorrect tyep, expecting named tuple"
        self._conv_cfg = val

    @property
    def batch_norm_en(self):
        return self._batch_norm_en

    @batch_norm_en.setter
    def batch_norm_en(self, val):
        assert isinstance(val, bool), "Error: incorrect type, expecting bool"
        self._batch_norm_en = val

    @property
    def repl_bias(self):
        return self._repl_bias

    @repl_bias.setter
    def repl_bias(self, val):
        assert isinstance(val, bool), "Error: incorrect type, expecting bool"
        self._repl_bias = val

    @property
    def bias_en(self):
        return self._bias_en

    @bias_en.setter
    def bias_en(self, val):
        assert isinstance(val, bool), "Error: incorrect type, expecting bool"
        self._bias_en = val

    @property
    def tens_trans_dims(self):
        return self._tens_trans_dims

    @tens_trans_dims.setter
    def tens_trans_dims(self, val):
        for op in val:
            for dim in op:
                assert isinstance(dim, int) and dim >= 0 and dim < 2**C_TENS_DIM_WDT, "Error: incorrect range"
        self._tens_trans_dims = val

    @property
    def mtx_trans_dims(self):
        return self._mtx_trans_dims

    @mtx_trans_dims.setter
    def mtx_trans_dims(self, val):
        for op in val:
            for dim in op:
                assert isinstance(dim, int) and dim >= 0 and dim < 2**C_TENS_DIM_WDT, "Error: incorrect range"
        self._mtx_trans_dims = val

    @property
    def tens_trans_addrs(self):
        return self._tens_trans_addrs

    @tens_trans_addrs.setter
    def tens_trans_addrs(self, val):
        for addr in val:
            assert isinstance(addr, int) and addr >= 0 and addr < 2**C_MMEM_ADDR_WDT, "Error: incorrect range"
        self._tens_trans_addrs = val

class tens_t():
    def __init__(self):
        self._name        = None
        self._dims        = None
        self._mtx_dims    = None
        self._layout      = None
        self._addr        = None
        self._block_index = None
        self._data_real   = None
        self._data_accel  = None

    @property
    def name(self):
        return self._name

    @name.setter
    def name(self, val):
        assert isinstance(val, str) and val, "Error: incorrect type, expecting non-empty string"
        self._name = val

    @property
    def dims(self):
        return self._dims

    @dims.setter
    def dims(self, val):
        for dim in val:
            assert isinstance(dim, int) and dim >= 0 and dim < 2**C_TENS_DIM_WDT, "Error: incorrect range"
        self._dims = val

    @property
    def mtx_dims(self):
        return self._dims

    @mtx_dims.setter
    def mtx_dims(self, val):
        for dim in val:
            assert isinstance(dim, int) and dim >= 0 and dim < 2**C_TENS_DIM_WDT, "Error: incorrect range"
        self._dims = val

    @property
    def layout(self):
        return self._layout

    @layout.setter
    def layout(self, val):
        assert isinstance(val, layout_t), "Error: incorrect type, expecting enum"
        self._layout = val

    @property
    def addr(self):
        return self._addr

    @addr.setter
    def addr(self, val):
        assert isinstance(val, int) and val >= 0 and val < 2**C_MMEM_ADDR_WDT, "Error: incorrect range"
        self._addr = val

    @property
    def block_index(self):
        return self._block_index

    @block_index.setter
    def block_index(self, val):
        assert isinstance(val, int) and val >= 0, "Error: incorrect range"
        self._block_index = val

    @property
    def data_real(self):
        return self._data_real

    @data_real.setter
    def data_real(self, val):
        for i, dim in enumerate(self._dims):
            if(dim != 0):
                assert dim == val.shape[i], "Error: incorrect dimensions"
        self._data_real = val

    @property
    def data_accel(self):
        return self._data_accel

    @data_accel.setter
    def data_accel(self, val):
        for i, dim in enumerate(self._dims):
            if(dim != 0):
                assert dim == val.shape[i], "Error: incorrect dimensions"
        self._data_accel = val

class tens_trans_t():
    def __init__(self):
        self._tens_gen_set       = []
        self._tens_use_set       = []
        self._tens_live_set      = []
        self._tens_trans_spec    = None
        self._src_a_name         = None
        self._src_b_name         = None
        self._bias_name          = None
        self._batch_name         = None
        self._res_name           = None
        self._src_val            = None
        self.h2c_data_source     = None

    @property
    def tens_gen_set(self):
        return self._tens_gen_set

    @tens_gen_set.setter
    def tens_gen_set(self, val):
        for lmnt in val:
            assert isinstance(lmnt, tens_t), "Error: incorrect type, expecting tens_t"
        self._tens_gen_set = val

    @property
    def tens_use_set(self):
        return self._tens_use_set

    @tens_use_set.setter
    def tens_use_set(self, val):
        for lmnt in val:
            assert isinstance(lmnt, tens_t), "Error: incorrect type, expecting tens_t"
        self._tens_use_set = val

    @property
    def tens_live_set(self):
        return self._tens_live_set

    @tens_live_set.setter
    def tens_live_set(self, val):
        for lmnt in val:
            assert isinstance(lmnt, tens_t), "Error: incorrect type, expecting tens_t"
        self._tens_live_set = val

    @property
    def tens_trans_spec(self):
        return self._tens_trans_spec

    @tens_trans_spec.setter
    def tens_trans_spec(self, val):
        assert isinstance(val, tens_trans_spec_t), "Error: incorrect type, expecting tens_trans_spec_t"
        self._tens_trans_spec = val

    @property
    def src_a_name(self):
        return self._src_a_name

    @src_a_name.setter
    def src_a_name(self, val):
        assert isinstance(val, str) and val, "Error: incorrect type, expecting non-empty string"
        self._src_a_name = val

    @property
    def src_b_name(self):
        return self._src_b_name

    @src_b_name.setter
    def src_b_name(self, val):
        assert isinstance(val, str) and val, "Error: incorrect type, expecting non-empty string"
        self._src_b_name = val

    @property
    def bias_name(self):
        return self._bias_name

    @bias_name.setter
    def bias_name(self, val):
        assert isinstance(val, str) and val, "Error: incorrect type, expecting non-empty string"
        self._bias_name = val

    @property
    def batch_name(self):
        return self._batch_name

    @batch_name.setter
    def batch_name(self, val):
        assert isinstance(val, str) and val, "Error: incorrect type, expecting non-empty string"
        self._batch_name = val

    @property
    def res_name(self):
        return self._res_name

    @res_name.setter
    def res_name(self, val):
        assert isinstance(val, str) and val, "Error: incorrect type, expecting non-empty string"
        self._res_name = val

class tens_trans_seq_t():
    def __init__(self):
        self._name            = None
        self._predecessor     = None
        self._tens_trans_set  = []

    @property
    def name(self):
        return self._name

    @name.setter
    def name(self, val):
        assert isinstance(val, str) and val, "Error: incorrect type, expecting non-empty string"
        self._name = val

    @property
    def predecessor(self):
        return self._predecessor

    @predecessor.setter
    def predecessor(self, val):
        assert isinstance(val, tens_trans_seq_t), "Error: incorrect type, expecting tens_trans_seq_t"
        self._predecessor = val

    @property
    def tens_trans_set(self):
        return self._tens_trans_set

    @tens_trans_set.setter
    def tens_trans_set(self, val):
        for lmnt in val:
            assert isinstance(lmnt, tens_trans_t), "Error: incorrect type, expecting tens_trans_t"
        self._tens_trans_set = val

class mem_block_t:
    def __init__(self, block_index, start_address, size):
        self.block_index = block_index
        self.start_address = start_address
        self.size = size
        self.free = True  

class mem_alloc_t:
    def __init__(self, mem_size):
        self.mem_size = mem_size
        self.blocks = [mem_block_t(0, 0, mem_size)]  
        self.next_index = 0 

    def allocate(self, size):
        for block in self.blocks:
            if block.free and block.size >= size:
                if block.size > size:
                    #create new child block, insert before the parent block
                    self.next_index += 1
                    new_block = mem_block_t(self.next_index, block.start_address, size)
                    new_block.free = False
                    self.blocks.insert(next((index for index, element in enumerate(self.blocks) if element.block_index == block.block_index)), new_block)
                    #modify the parent block
                    block.start_address = block.start_address + size
                    block.size          = block.size - size
                    return new_block.block_index, new_block.start_address
                else:
                    block.free = False
                    return block.block_index, block.start_address
        
        assert False, "Error, not enough memory to allocate"

    def deallocate(self, block_index):
        block = next((block for block in self.blocks if block.block_index == block_index), None)
        if block is not None:
            block.free = True
            # Merge consecutive free blocks
            self.merge_free_blocks()
        else:
            raise IndexError("Invalid block index")

    def merge_free_blocks(self):
        i = 0
        while i < len(self.blocks) - 1:
            if self.blocks[i].free and self.blocks[i + 1].free:
                self.blocks[i].size += self.blocks[i + 1].size
                del self.blocks[i + 1]
            else:
                i += 1

class stream_trans_t:
    def __init__(self, data_real, data_accel, name, offset, len):
        self.data_real = data_real
        self.data_accel = data_accel
        self.name = name
        self.offset = offset
        self.len = len
