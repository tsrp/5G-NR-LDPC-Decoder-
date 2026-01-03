# ==============================================================================
# SDC Constraints File for 5G NR LDPC Decoder
# Synopsys Design Constraints for synthesis and implementation
# ==============================================================================

# ==============================================================================
# Clock Definition
# ==============================================================================

# Primary clock: 230 MHz (4.35 ns period)
# Target frequency based on paper specifications
create_clock -name clk -period 4.35 [get_ports clk]

# Clock uncertainty (jitter + skew)
set_clock_uncertainty 0.2 [get_clocks clk]

# Clock transition time
set_clock_transition 0.1 [get_clocks clk]

# ==============================================================================
# Input/Output Delays
# ==============================================================================

# Input delays (relative to clock edge)
# Assume inputs arrive 0.5 ns after clock edge
set_input_delay -clock clk -max 0.5 [all_inputs]
set_input_delay -clock clk -min 0.2 [all_inputs]

# Remove delay from clock and reset
set_input_delay 0 -clock clk [get_ports clk]
set_input_delay 0 -clock clk [get_ports rst_n]

# Output delays (relative to clock edge)
# Assume outputs must be stable 0.5 ns before next clock edge
set_output_delay -clock clk -max 0.5 [all_outputs]
set_output_delay -clock clk -min 0.2 [all_outputs]

# ==============================================================================
# Input/Output Drive Strength and Load
# ==============================================================================

# Input drive strength (assume driven by standard cell)
# set_driving_cell -lib_cell BUFX2 -library tcbn65lpwc [all_inputs]
set_drive 1.0 [all_inputs]

# Output load (assume driving standard load)
# set_load [load_of tcbn65lpwc/BUFX2/A] [all_outputs]
set_load 0.05 [all_outputs]

# ==============================================================================
# Environmental Conditions
# ==============================================================================

# Operating conditions
# set_operating_conditions -max WCCOM -min BCCOM

# Temperature and voltage
# set_temperature 125
# set_voltage 1.08 -min 0.99

# Wire load model
# set_wire_load_model -name "suggested" -library tcbn65lpwc

# ==============================================================================
# Design Rule Constraints
# ==============================================================================

# Maximum transition time (slew rate)
set_max_transition 0.5 [current_design]

# Maximum fanout
set_max_fanout 16 [current_design]

# Maximum capacitance
set_max_capacitance 0.5 [all_outputs]

# ==============================================================================
# Area Constraints
# ==============================================================================

# Set maximum area (0 means minimize)
set_max_area 0

# ==============================================================================
# Timing Exceptions
# ==============================================================================

# False paths (if any)
# Example: Configuration signals that don't need to meet timing
# set_false_path -from [get_ports config_enable]
# set_false_path -from [get_ports code_rate_sel]

# Multicycle paths (if any)
# Example: Configuration memory writes can take 2 cycles
# set_multicycle_path 2 -setup -from [get_ports write_enable]
# set_multicycle_path 1 -hold -from [get_ports write_enable]

# ==============================================================================
# Clock Groups (if multiple clocks exist)
# ==============================================================================

# Define asynchronous clock groups if needed
# set_clock_groups -asynchronous -group [get_clocks clk] -group [get_clocks config_clk]

# ==============================================================================
# Case Analysis (for synthesis optimization)
# ==============================================================================

# If certain control signals have known values during normal operation
# Example: Always use normalized min-sum
# set_case_analysis 1 [get_ports use_offset]

# ==============================================================================
# Don't Touch (preserve certain logic)
# ==============================================================================

# Preserve critical path logic if needed
# set_dont_touch [get_cells u_vn_decoder/critical_path_reg]

# ==============================================================================
# Compile Directives
# ==============================================================================

# Optimization effort
# set_compile_effort high

# Flatten hierarchy for better optimization (use cautiously)
# set_flatten true -effort high

# Enable retiming
# set_optimize_registers true

# ==============================================================================
# Power Optimization
# ==============================================================================

# Clock gating
set_clock_gating_style -sequential_cell latch -num_stages 1

# Dynamic power optimization
# set_dynamic_optimization true

# Leakage power optimization
# set_leakage_optimization true

# ==============================================================================
# Specific Path Constraints
# ==============================================================================

# Critical paths that need special attention

# 1. VN to CN message path
# set_max_delay 4.0 -from [get_pins u_vn_decoder/vn_messages_reg*/Q] \
#                   -to [get_pins u_cn_decoder/vn_messages_reg*/D]

# 2. Barrel shifter path
# set_max_delay 3.5 -from [get_pins u_barrel_shifter/stage1_reg*/Q] \
#                   -to [get_pins u_barrel_shifter/stage2_reg*/D]

# 3. Min-finding path in CND
# set_max_delay 3.8 -from [get_pins u_cn_decoder/msg_memory_reg*/Q] \
#                   -to [get_pins u_cn_decoder/min1_reg*/D]

# ==============================================================================
# Memory Constraints
# ==============================================================================

# Configuration memories (if using BRAM)
# set_dont_use [get_lib_cells *ROM*]  # Use RAM instead of ROM

# ==============================================================================
# I/O Standards (for FPGA implementation)
# ==============================================================================

# Xilinx Kintex-7 specific
# set_property IOSTANDARD LVCMOS18 [get_ports *]
# set_property PACKAGE_PIN AA12 [get_ports clk]
# set_property PACKAGE_PIN AB12 [get_ports rst_n]

# ==============================================================================
# Timing Reports to Generate
# ==============================================================================

# After synthesis, generate these reports:
# report_timing -max_paths 10 -nworst 1 -delay_type max
# report_timing -max_paths 10 -nworst 1 -delay_type min
# report_constraint -all_violators
# report_area -hierarchy
# report_power -hierarchy
# report_clock_gating
# report_resources

# ==============================================================================
# Notes
# ==============================================================================

# 1. Adjust clock period based on synthesis results
#    - If timing is met with margin, can increase frequency
#    - If timing fails, may need to reduce frequency or optimize
#
# 2. For FPGA implementation:
#    - Use Vivado XDC format instead of SDC
#    - Add placement constraints for critical paths
#    - Consider using BRAM for configuration memories
#
# 3. For ASIC implementation:
#    - Uncomment library-specific constraints
#    - Add scan chain constraints for DFT
#    - Include power domain specifications
#
# 4. Critical paths to watch:
#    - VN message accumulation (adder tree)
#    - CN min-finding logic (comparator tree)
#    - Barrel shifter routing (high fanout)
#    - Configuration memory access
#
# 5. Optimization strategies:
#    - Pipeline critical paths if timing fails
#    - Reduce parallelism factor F to save resources
#    - Use clock gating for power savings
#    - Consider layered decoding for reduced latency

# ==============================================================================
# End of Constraints File
# ==============================================================================
