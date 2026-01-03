// ============================================================================
// Testbench for 5G NR LDPC Decoder
// Simulates BPSK-AWGN channel with configurable SNR
// ============================================================================

`timescale 1ns/1ps

module ldpc_decoder_tb;

    import ldpc_decoder_pkg::*;
    
    // ========================================================================
    // Parameters
    // ========================================================================
    
    parameter int CLK_PERIOD = 4;  // 250 MHz clock (4ns period)
    parameter int Z = 56;
    parameter int DATA_WIDTH = 6;
    parameter real SNR_DB = 3.2;  // Eb/N0 in dB
    parameter int NUM_FRAMES = 10;
    
    // ========================================================================
    // Signals
    // ========================================================================
    
    logic                        clk;
    logic                        rst_n;
    logic                        start_decode;
    logic [2:0]                  code_rate_sel;
    logic [8:0]                  lifting_factor_z;
    logic [3:0]                  base_graph_sel;
    logic [4:0]                  max_iter;
    
    logic signed [DATA_WIDTH-1:0] llr_in[Z-1:0];
    logic                         llr_valid;
    
    logic                         decoded_bit[Z-1:0];
    logic                         decode_valid;
    logic                         decode_done;
    
    logic [4:0]                   iterations_used;
    logic                         parity_check_passed;
    logic                         decode_success;
    
    logic [31:0]                  cycle_count;
    logic [15:0]                  throughput_mbps;
    
    // Test variables
    logic [Z-1:0]                 tx_bits;
    logic [Z-1:0]                 rx_bits;
    int                           bit_errors;
    int                           frame_errors;
    int                           total_bits;
    int                           total_frames;
    real                          ber;
    real                          fer;
    
    // ========================================================================
    // Clock Generation
    // ========================================================================
    
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // ========================================================================
    // DUT Instantiation
    // ========================================================================
    
    ldpc_decoder_top #(
        .Z(Z),
        .MAX_ITERATIONS(15),
        .DATA_WIDTH(DATA_WIDTH),
        .PARALLELISM_FACTOR(4),
        .MAX_VN_DEGREE(19),
        .MAX_CN_DEGREE(30),
        .NORMALIZATION_ALPHA(192)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .start_decode(start_decode),
        .code_rate_sel(code_rate_sel),
        .lifting_factor_z(lifting_factor_z),
        .base_graph_sel(base_graph_sel),
        .max_iter(max_iter),
        .llr_in(llr_in),
        .llr_valid(llr_valid),
        .decoded_bit(decoded_bit),
        .decode_valid(decode_valid),
        .decode_done(decode_done),
        .iterations_used(iterations_used),
        .parity_check_passed(parity_check_passed),
        .decode_success(decode_success),
        .cycle_count(cycle_count),
        .throughput_mbps(throughput_mbps)
    );
    
    // ========================================================================
    // AWGN Channel Model
    // ========================================================================
    
    function real gaussian_noise();
        real u1, u2, z;
        u1 = $urandom_range(1, 1000000) / 1000000.0;
        u2 = $urandom_range(1, 1000000) / 1000000.0;
        z = $sqrt(-2.0 * $ln(u1)) * $cos(2.0 * 3.14159265359 * u2);
        return z;
    endfunction
    
    function logic signed [DATA_WIDTH-1:0] generate_llr(
        input logic bit_value,
        input real snr_db
    );
        real signal, noise, received, llr_float;
        real snr_linear, noise_variance;
        logic signed [DATA_WIDTH-1:0] llr_quantized;
        
        // Convert SNR from dB to linear
        snr_linear = 10.0 ** (snr_db / 10.0);
        noise_variance = 1.0 / (2.0 * snr_linear);
        
        // BPSK modulation: 0 -> +1, 1 -> -1
        signal = bit_value ? -1.0 : 1.0;
        
        // Add AWGN
        noise = gaussian_noise() * $sqrt(noise_variance);
        received = signal + noise;
        
        // Compute LLR: log(P(x=0|y) / P(x=1|y))
        llr_float = (2.0 * received) / noise_variance;
        
        // Quantize to DATA_WIDTH bits (saturation)
        if (llr_float > (2**(DATA_WIDTH-1) - 1)) begin
            llr_quantized = 2**(DATA_WIDTH-1) - 1;
        end else if (llr_float < -(2**(DATA_WIDTH-1))) begin
            llr_quantized = -(2**(DATA_WIDTH-1));
        end else begin
            llr_quantized = $rtoi(llr_float);
        end
        
        return llr_quantized;
    endfunction
    
    // ========================================================================
    // Test Stimulus
    // ========================================================================
    
    initial begin
        // Initialize
        rst_n = 0;
        start_decode = 0;
        code_rate_sel = 3'b000;  // Rate 1/3
        lifting_factor_z = 9'd56;
        base_graph_sel = 4'd1;   // BG1
        max_iter = 5'd15;
        llr_valid = 0;
        
        bit_errors = 0;
        frame_errors = 0;
        total_bits = 0;
        total_frames = 0;
        
        // Reset
        #(CLK_PERIOD * 10);
        rst_n = 1;
        #(CLK_PERIOD * 5);
        
        $display("========================================");
        $display("5G NR LDPC Decoder Testbench");
        $display("========================================");
        $display("Configuration:");
        $display("  Lifting Factor Z: %0d", Z);
        $display("  Code Rate: 1/3");
        $display("  Base Graph: BG1");
        $display("  SNR (Eb/N0): %.1f dB", SNR_DB);
        $display("  Max Iterations: %0d", max_iter);
        $display("  Number of Frames: %0d", NUM_FRAMES);
        $display("========================================\n");
        
        // Test multiple frames
        for (int frame = 0; frame < NUM_FRAMES; frame++) begin
            $display("Frame %0d:", frame);
            
            // Generate random transmitted bits
            for (int i = 0; i < Z; i++) begin
                tx_bits[i] = $urandom_range(0, 1);
            end
            
            // Generate LLRs through AWGN channel
            for (int i = 0; i < Z; i++) begin
                llr_in[i] = generate_llr(tx_bits[i], SNR_DB);
            end
            
            // Start decoding
            llr_valid = 1;
            start_decode = 1;
            #(CLK_PERIOD);
            start_decode = 0;
            
            // Wait for decoding to complete
            wait(decode_done);
            #(CLK_PERIOD);
            llr_valid = 0;
            
            // Check results
            for (int i = 0; i < Z; i++) begin
                rx_bits[i] = decoded_bit[i];
                if (tx_bits[i] != rx_bits[i]) begin
                    bit_errors++;
                end
            end
            
            total_bits += Z;
            total_frames++;
            
            if (!decode_success) begin
                frame_errors++;
            end
            
            // Display frame results
            $display("  Iterations: %0d", iterations_used);
            $display("  Parity Check: %s", parity_check_passed ? "PASS" : "FAIL");
            $display("  Decode Success: %s", decode_success ? "YES" : "NO");
            $display("  Cycle Count: %0d", cycle_count);
            $display("  Throughput: %0d Mbps", throughput_mbps);
            $display("  Bit Errors: %0d / %0d\n", bit_errors, total_bits);
            
            // Wait before next frame
            #(CLK_PERIOD * 10);
        end
        
        // Calculate final statistics
        ber = real'(bit_errors) / real'(total_bits);
        fer = real'(frame_errors) / real'(total_frames);
        
        $display("========================================");
        $display("Final Statistics:");
        $display("========================================");
        $display("Total Frames: %0d", total_frames);
        $display("Frame Errors: %0d", frame_errors);
        $display("Total Bits: %0d", total_bits);
        $display("Bit Errors: %0d", bit_errors);
        $display("BER: %.2e", ber);
        $display("FER: %.2e", fer);
        $display("Average Throughput: %0d Mbps", throughput_mbps);
        $display("========================================\n");
        
        // Check against target BER
        if (ber < 1e-5) begin
            $display("TEST PASSED: BER < 10^-5 at %.1f dB", SNR_DB);
        end else begin
            $display("TEST INFO: BER = %.2e at %.1f dB", ber, SNR_DB);
        end
        
        #(CLK_PERIOD * 100);
        $finish;
    end
    
    // ========================================================================
    // Waveform Dump
    // ========================================================================
    
    initial begin
        $dumpfile("ldpc_decoder_tb.vcd");
        $dumpvars(0, ldpc_decoder_tb);
    end
    
    // ========================================================================
    // Timeout Watchdog
    // ========================================================================
    
    initial begin
        #(CLK_PERIOD * 1000000);  // 4ms timeout
        $display("ERROR: Simulation timeout!");
        $finish;
    end
    
    // ========================================================================
    // Performance Monitoring
    // ========================================================================
    
    real avg_latency;
    int total_cycles;
    
    always @(posedge clk) begin
        if (decode_done) begin
            total_cycles += cycle_count;
        end
    end
    
    final begin
        if (total_frames > 0) begin
            avg_latency = real'(total_cycles) / real'(total_frames);
            $display("Average Latency: %.2f cycles/frame", avg_latency);
        end
    end

endmodule : ldpc_decoder_tb
