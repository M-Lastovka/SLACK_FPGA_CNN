# eff_FPGA_CNN_impl_master_thesis 

## Project description

+ Project name:          Efficient FPGA CNN implementation
+ Project author:        Martin Lastovka: martin.lastovka@dsp.rwth-aachen.de
+ Project supervisor:    Mohsen Pourghasemian: mohsen@dsp.rwth-aachen.de
+ Institution:           Chair for Distributed Signal Processing
+ Project version:       1.0
+ Tested Vivado version: 2021.1

## General description

This project was developed as a master thesis of Martin Lastovka @ RWTH Aachen in 2024.

The project is a fully parametrizable, programmable CNN accelerator meant to be deployed on a FPGA platform. The IP was designed for very low-latency, high performance inference. 

Apart from the SystemVerilog RTL description of the accelerator, this project features Python code to parse a our own YAML model description and then generate needed memory-mapped transactions (register configurations) and H2C binaries for simulation and testing. Additionally, the accelerator C2H binaries (either originating from simulation or testing) can be compared to a reduced-precision model as well as an reference model.

Lastly, this project includes C driver for the accelerator, for configuring and reading its registers, scheduling H2C and C2H transfers and synchronization. The driver is split into abstract (platform agnostic) portion and device-specific (Xilinx Zynq) portion.

## Key features

+ Systolic-array based accelerator
+ Conv2d supported (except for dilation)
+ BatchNorm2d supported
+ MaxPool2d supported (except for dilation)
+ Linear supported
+ Tensor flattening supported (limited)
+ Tanh and ReLu activations supported
+ Simple, single wide bus pipeline with distributed control and backpressure
+ Programmable using simple set of instructions

## This document describes

TODO

## Repo file structure

+ **design/**: All SLACK RTL sources.
    + **rtl/**: SLACK RTL sources.
    + **rtl_pckg/**: SLACK RTL packages.
+ **doc/**: Documentation: SLACK register map description, YAML internal format description.
+ **sim/**: SystemVerilog testbench.
+ **sw**: PS code and scripts
    + **dnn_model/**: PyTorch model to be run.
    + **ps/**: SLACK driver.
    + **regmap_scripts**: Corsair scripts to generate register map RTL, C headers, Python headers.
    + **sim_scripts**: Generate and process simulation test patterns based on YAML. RTL generation.
+ **vivado**: All sources involving Vivado.
    + **build_script**: Scripts for building the Vivado project.
    + **constr**: Vivado constraints.
    + **ip_src**: Vivado IP dependencies.
    + **wave_configs**: Vivado simulator waveform configuration.

## Building and running simulation

Steps how to run and build the example simulation:

+ CD to *./vivado/build_script/* and execute *eff_cnn_fpga_build.tcl* with Vivado. This will build the Vivado project. Tested with Vivado 2021.1 on Windows 10.
+ Execute the script *./sw/sim_scripts/cnn_sim.py* with the default arguments. Based on the tensor transformation sequence specification in *test_model_spec.yaml*, RTL files, LUT tables, simulation control files, and simulation inputs (memory-mapped and stream transactions) will be generated.
    + *cnn_sim.py* has some dependencies, notably the fixed-point library fxpmath and numpy.
    + The sequence in *test_model_spec.yaml* implements a simple CNN with a single convolutional layer and a single fully connected layer, the inputs and weights are random gaussian noise. A more complex example is shown in *test_model_spec_v16_CIFAR10.yaml*.
+ Modify the project origin path variable *C_PROJ_PATH* in *./sim/testbench/tb_pckg.sv*.
+ Run the behavioral simulation in Vivado, this should take only around 15us of simulation time. Verify that a file called *test_c2h_stream.bin* has been generated
+ Execute the script *./sw/sim_scripts/cnn_sim.py* with the the *mode* argument set to *s_out*. The simulation outputs will be compared against a fixed point model (zero error expected) and a real mode (small error expected).

## System-level integration and running Bitstream

TODO

