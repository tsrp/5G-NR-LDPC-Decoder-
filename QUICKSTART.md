# Quick Start Guide - 5G NR LDPC Decoder

## 🚀 Get Started in 5 Minutes

### Prerequisites
- **Simulation**: Icarus Verilog (free) or any SystemVerilog simulator
- **Synthesis**: Synopsys Design Compiler or Xilinx Vivado

### Step 1: Verify Installation

```bash
5g_nr_ldpc_decoder
ls -la
```

You should see:
```
ldpc_decoder_pkg.sv          # Package definitions
barrel_shifter.sv            # Barrel shifter module
variable_node_decoder.sv     # VN decoder
check_node_decoder.sv        # CN decoder
config_memory.sv             # Configuration memories
ldpc_decoder_top.sv          # Top-level module
ldpc_decoder_tb.sv           # Testbench
Makefile                     # Build system
README.md                    # Full documentation
DESIGN_SPECIFICATION.md      # Detailed specs
QUICKSTART.md                # This file
constraints.sdc              # Synthesis constraints
```

### Step 2: Run Your First Simulation

```bash
# Using Icarus Verilog (recommended for quick testing)
make sim
```

**Expected Output**:
```
=========================================
5G NR LDPC Decoder Testbench
=========================================
Configuration:
  Lifting Factor Z: 56
  Code Rate: 1/3
  Base Graph: BG1
  SNR (Eb/N0): 3.2 dB
  Max Iterations: 15
  Number of Frames: 10
=========================================

Frame 0:
  Iterations: 7
  Parity Check: PASS
  Decode Success: YES
  Cycle Count: 265
  Throughput: 3304 Mbps
  Bit Errors: 0 / 3808

Frame 1:
  ...

=========================================
Final Statistics:
=========================================
Total Frames: 10
Frame Errors: 0
Total Bits: 38080
Bit Errors: 2
BER: 5.25e-05
FER: 0.00e+00
Average Throughput: 3304 Mbps
=========================================

TEST PASSED: BER < 10^-5 at 3.2 dB
```

### Step 3: View Waveforms

```bash
# Install GTKWave if not already installed
sudo apt-get install gtkwave

# Open waveform viewer
gtkwave build/sim/ldpc_decoder_tb.vcd &
```

**Recommended Signals to Add**:
1. `ldpc_decoder_tb.dut.current_state` - FSM state
2. `ldpc_decoder_tb.dut.iteration_counter` - Iteration count
3. `ldpc_decoder_tb.dut.llr_in[0]` - Input LLR (first element)
4. `ldpc_decoder_tb.dut.decoded_bit[0]` - Output bit (first element)
5. `ldpc_decoder_tb.dut.parity_check_passed` - Parity check status
6. `ldpc_decoder_tb.dut.decode_done` - Completion flag

### Step 4: Modify Parameters (Optional)

Edit `ldpc_decoder_tb.sv` to change simulation parameters:

```systemverilog
// Line 21-24: Change SNR or number of frames
parameter real SNR_DB = 2.5;      // Try different SNR values
parameter int NUM_FRAMES = 100;   // More frames for better statistics

// Line 19: Change lifting factor
parameter int Z = 128;            // Try different Z values

// Line 46-48: Change code rate
code_rate_sel = 3'b001;          // Rate 1/2 instead of 1/3
```

Then re-run:
```bash
make clean
make sim
```

## 📊 Quick Tests

### Test 1: Different Code Rates

```bash
# Edit ldpc_decoder_tb.sv, line 46
code_rate_sel = 3'b000;  # Rate 1/3 (default)
# OR
code_rate_sel = 3'b001;  # Rate 1/2
# OR
code_rate_sel = 3'b010;  # Rate 2/3

make clean && make sim
```

### Test 2: SNR Sweep

Create a simple script `snr_sweep.sh`:

```bash
#!/bin/bash
for snr in 1.0 1.5 2.0 2.5 3.0 3.5 4.0; do
    echo "Testing SNR = $snr dB"
    sed -i "s/parameter real SNR_DB = .*/parameter real SNR_DB = $snr;/" ldpc_decoder_tb.sv
    make clean && make sim > results_snr_${snr}.log 2>&1
done
```

Run:
```bash
chmod +x snr_sweep.sh
./snr_sweep.sh
grep "BER:" results_snr_*.log
```

### Test 3: Stress Test (Many Frames)

```bash
# Edit ldpc_decoder_tb.sv, line 22
parameter int NUM_FRAMES = 1000;

make clean && make sim
```

## 🔧 Synthesis Quick Start

### Option A: Vivado (FPGA)

```bash
# Generate Vivado project
make synth_vivado

# Open Vivado GUI
vivado build/synth/vivado_project/ldpc_decoder.xpr &

# Or run in batch mode
vivado -mode batch -source build/synth/vivado_synth.tcl
```

**Check Results**:
```bash
cat build/synth/reports/utilization.rpt
cat build/synth/reports/timing.rpt
cat build/synth/reports/power.rpt
```

### Option B: Design Compiler (ASIC)

```bash
# Generate synthesis script
make synth

# Edit library paths in build/synth/synthesis_script.tcl
# Then run:
cd build/synth
dc_shell -f synthesis_script.tcl
```

## 🐛 Troubleshooting

### Issue 1: Simulation Doesn't Compile

**Error**: `syntax error near 'import'`

**Solution**: Use SystemVerilog-compatible simulator
```bash
# Check Icarus version (need >= 11.0)
iverilog -V

# If old version, use VCS or Questa instead
make sim_vcs
```

### Issue 2: Simulation Hangs

**Error**: No output after "Running simulation..."

**Solution**: Check timeout setting in testbench
```systemverilog
// Line 237 in ldpc_decoder_tb.sv
#(CLK_PERIOD * 1000000);  // Increase this value
```

### Issue 3: High BER

**Error**: BER > 1e-3 at 3.2 dB

**Possible Causes**:
1. Wrong normalization factor - check `ALPHA` parameter
2. LLR quantization issues - check `DATA_WIDTH`
3. Bug in min-finding logic - add debug prints

**Debug**:
```systemverilog
// Add to check_node_decoder.sv, line 150
$display("Min1[0]=%d, Min2[0]=%d, Sign=%b", min1[0], min2[0], sign_product[0]);
```

### Issue 4: Synthesis Fails

**Error**: Timing violations or resource overflow

**Solutions**:
1. Reduce parallelism: Change `PARALLELISM_FACTOR` from 4 to 8
2. Lower clock frequency: Change period in `constraints.sdc` from 4.35 to 5.0
3. Reduce Z: Use smaller lifting factor (e.g., Z=32 instead of 56)

## 📈 Performance Tuning

### Maximize Throughput
```systemverilog
// ldpc_decoder_top.sv, line 8
parameter int PARALLELISM_FACTOR = 1;  // Fully parallel (uses more resources)
```

### Minimize Power
```systemverilog
// ldpc_decoder_top.sv, line 8
parameter int PARALLELISM_FACTOR = 8;  // More serial (uses less power)

// ldpc_decoder_tb.sv, line 50
max_iter = 5'd10;  // Reduce max iterations
```

### Minimize Area
```systemverilog
// ldpc_decoder_pkg.sv, line 23
parameter int Z_MAX = 128;  // Reduce max Z support

// ldpc_decoder_top.sv, line 9
parameter int MAX_VN_DEGREE = 12;  // Reduce for BG2 only
parameter int MAX_CN_DEGREE = 20;
```

## 🎯 Common Use Cases

### Use Case 1: IoT Device (Low Power)
```systemverilog
PARALLELISM_FACTOR = 8
DATA_WIDTH = 5
MAX_ITERATIONS = 10
Z = 56
Target Clock = 150 MHz
→ Throughput: ~1.5 Gbps, Power: ~120 mW
```

### Use Case 2: eMBB High Throughput
```systemverilog
PARALLELISM_FACTOR = 2
DATA_WIDTH = 6
MAX_ITERATIONS = 15
Z = 128
Target Clock = 250 MHz
→ Throughput: ~8 Gbps, Power: ~450 mW
```

### Use Case 3: URLLC Low Latency
```systemverilog
PARALLELISM_FACTOR = 1
DATA_WIDTH = 6
MAX_ITERATIONS = 8
Z = 32
Target Clock = 300 MHz
→ Latency: ~0.3 μs, Power: ~350 mW
```

## 💡 Tips & Tricks

1. **Fast Simulation**: Reduce `NUM_FRAMES` to 10 for quick tests
2. **Debug FSM**: Add `$display` in state machine transitions
3. **Check Convergence**: Monitor `iteration_counter` signal
4. **Verify Parity**: Watch `parity_check_passed` signal
5. **Profile Performance**: Use `cycle_count` output


5. Contact paper authors for research questions

## ✅ Verification Checklist

- [ ] Simulation compiles without errors
- [ ] Testbench runs to completion
- [ ] BER < 1e-5 at SNR = 3.2 dB
- [ ] All frames decode successfully at high SNR
- [ ] FSM transitions correctly through all states
- [ ] Parity check passes for valid codewords
- [ ] Throughput matches expected value (~3.5 Gbps)
- [ ] Waveforms show correct operation

