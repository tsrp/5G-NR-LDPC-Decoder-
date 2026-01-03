# ============================================================================
# Makefile for 5G NR LDPC Decoder
# Supports simulation, synthesis, and implementation
# ============================================================================

# Tool Selection
SIM_TOOL ?= iverilog
SYNTH_TOOL ?= synopsys

# Directories
SRC_DIR = .
TB_DIR = .
BUILD_DIR = build
SIM_DIR = $(BUILD_DIR)/sim
SYNTH_DIR = $(BUILD_DIR)/synth

# Source Files
PKG_FILES = $(SRC_DIR)/ldpc_decoder_pkg.sv
RTL_FILES = $(SRC_DIR)/barrel_shifter.sv \
            $(SRC_DIR)/variable_node_decoder.sv \
            $(SRC_DIR)/check_node_decoder.sv \
            $(SRC_DIR)/config_memory.sv \
            $(SRC_DIR)/ldpc_decoder_top.sv

TB_FILES = $(TB_DIR)/ldpc_decoder_tb.sv

ALL_SV_FILES = $(PKG_FILES) $(RTL_FILES) $(TB_FILES)

# Simulation Parameters
TOP_MODULE = ldpc_decoder_tb
WAVES_FILE = $(SIM_DIR)/ldpc_decoder_tb.vcd

# Compiler Flags
IVERILOG_FLAGS = -g2012 -Wall -Winfloop
VCS_FLAGS = -full64 -sverilog +v2k -timescale=1ns/1ps -debug_access+all
XVLOG_FLAGS = -sv -work work

# ============================================================================
# Targets
# ============================================================================

.PHONY: all clean sim synth help

all: sim

help:
	@echo "5G NR LDPC Decoder Makefile"
	@echo "============================"
	@echo "Targets:"
	@echo "  make sim        - Run simulation with Icarus Verilog"
	@echo "  make sim_vcs    - Run simulation with Synopsys VCS"
	@echo "  make sim_questa - Run simulation with Mentor Questa"
	@echo "  make synth      - Synthesize with Synopsys Design Compiler"
	@echo "  make clean      - Clean build artifacts"
	@echo "  make help       - Show this help message"
	@echo ""
	@echo "Parameters:"
	@echo "  SIM_TOOL={iverilog|vcs|questa}"
	@echo "  SYNTH_TOOL={synopsys|vivado}"

# ============================================================================
# Simulation Targets
# ============================================================================

sim: $(SIM_DIR)
	@echo "========================================="
	@echo "Running simulation with Icarus Verilog"
	@echo "========================================="
	iverilog $(IVERILOG_FLAGS) -o $(SIM_DIR)/$(TOP_MODULE).vvp \
		-s $(TOP_MODULE) $(ALL_SV_FILES)
	cd $(SIM_DIR) && vvp $(TOP_MODULE).vvp
	@echo ""
	@echo "Simulation complete. Waveform: $(WAVES_FILE)"

sim_vcs: $(SIM_DIR)
	@echo "========================================="
	@echo "Running simulation with Synopsys VCS"
	@echo "========================================="
	cd $(SIM_DIR) && vcs $(VCS_FLAGS) \
		-top $(TOP_MODULE) \
		-o $(TOP_MODULE).simv \
		$(addprefix ../,$(ALL_SV_FILES))
	cd $(SIM_DIR) && ./$(TOP_MODULE).simv
	@echo "Simulation complete."

sim_questa: $(SIM_DIR)
	@echo "========================================="
	@echo "Running simulation with Mentor Questa"
	@echo "========================================="
	cd $(SIM_DIR) && vlib work
	cd $(SIM_DIR) && vlog $(XVLOG_FLAGS) $(addprefix ../,$(ALL_SV_FILES))
	cd $(SIM_DIR) && vsim -c -do "run -all; quit" $(TOP_MODULE)
	@echo "Simulation complete."

# ============================================================================
# Synthesis Targets
# ============================================================================

synth: $(SYNTH_DIR)
	@echo "========================================="
	@echo "Synthesizing with Synopsys DC"
	@echo "========================================="
	@echo "Creating synthesis script..."
	@$(MAKE) create_synth_script
	@echo "Note: Full synthesis requires Synopsys Design Compiler"
	@echo "      and TSMC 65nm library files."
	@echo ""
	@echo "To run synthesis:"
	@echo "  cd $(SYNTH_DIR)"
	@echo "  dc_shell -f synthesis_script.tcl"

create_synth_script: $(SYNTH_DIR)
	@echo "# Synopsys Design Compiler Script" > $(SYNTH_DIR)/synthesis_script.tcl
	@echo "# Generated for 5G NR LDPC Decoder" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "# Set design name" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "set design_name ldpc_decoder_top" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "# Load technology library" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "# set target_library \"tcbn65lpwc.db\"" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "# set link_library \"* tcbn65lpwc.db\"" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "# Read design files" >> $(SYNTH_DIR)/synthesis_script.tcl
	@for file in $(PKG_FILES) $(RTL_FILES); do \
		echo "analyze -format sverilog $$file" >> $(SYNTH_DIR)/synthesis_script.tcl; \
	done
	@echo "" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "elaborate \$$design_name" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "# Set constraints" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "create_clock -name clk -period 4.35 [get_ports clk]" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "set_input_delay -clock clk 0.5 [all_inputs]" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "set_output_delay -clock clk 0.5 [all_outputs]" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "# Compile design" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "compile_ultra" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "# Generate reports" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "report_area > reports/area.rpt" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "report_timing > reports/timing.rpt" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "report_power > reports/power.rpt" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "# Write outputs" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "write -format verilog -hierarchy -output outputs/\$$design_name.v" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "write_sdc outputs/\$$design_name.sdc" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "" >> $(SYNTH_DIR)/synthesis_script.tcl
	@echo "exit" >> $(SYNTH_DIR)/synthesis_script.tcl
	@mkdir -p $(SYNTH_DIR)/reports
	@mkdir -p $(SYNTH_DIR)/outputs

# ============================================================================
# Vivado Synthesis (Alternative)
# ============================================================================

synth_vivado: $(SYNTH_DIR)
	@echo "========================================="
	@echo "Creating Vivado project"
	@echo "========================================="
	@$(MAKE) create_vivado_script
	@echo "To run Vivado synthesis:"
	@echo "  vivado -mode batch -source $(SYNTH_DIR)/vivado_synth.tcl"

create_vivado_script: $(SYNTH_DIR)
	@echo "# Vivado Synthesis Script" > $(SYNTH_DIR)/vivado_synth.tcl
	@echo "# Create project" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "create_project ldpc_decoder $(SYNTH_DIR)/vivado_project -part xc7k325tffg900-2" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "# Add source files" >> $(SYNTH_DIR)/vivado_synth.tcl
	@for file in $(PKG_FILES) $(RTL_FILES); do \
		echo "add_files $$file" >> $(SYNTH_DIR)/vivado_synth.tcl; \
	done
	@echo "" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "# Set top module" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "set_property top ldpc_decoder_top [current_fileset]" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "# Create clock constraint" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "create_clock -period 4.35 -name clk [get_ports clk]" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "# Run synthesis" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "launch_runs synth_1" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "wait_on_run synth_1" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "# Generate reports" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "open_run synth_1" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "report_utilization -file $(SYNTH_DIR)/reports/utilization.rpt" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "report_timing_summary -file $(SYNTH_DIR)/reports/timing.rpt" >> $(SYNTH_DIR)/vivado_synth.tcl
	@echo "report_power -file $(SYNTH_DIR)/reports/power.rpt" >> $(SYNTH_DIR)/vivado_synth.tcl

# ============================================================================
# Directory Setup
# ============================================================================

$(SIM_DIR):
	mkdir -p $(SIM_DIR)

$(SYNTH_DIR):
	mkdir -p $(SYNTH_DIR)
	mkdir -p $(SYNTH_DIR)/reports
	mkdir -p $(SYNTH_DIR)/outputs

# ============================================================================
# Clean
# ============================================================================

clean:
	@echo "Cleaning build artifacts..."
	rm -rf $(BUILD_DIR)
	rm -f *.vcd *.vvp *.log
	rm -rf work csrc simv* ucli.key
	@echo "Clean complete."

# ============================================================================
# Lint (Optional)
# ============================================================================

lint:
	@echo "Running Verilator lint..."
	verilator --lint-only -Wall --top-module ldpc_decoder_top \
		$(PKG_FILES) $(RTL_FILES)
	@echo "Lint complete."
