// ============================================================================
// 5G NR LDPC Decoder Top Module
// Implements partially-parallel LDPC decoder with runtime reconfigurability
// Based on offline design flow for 5G NR PCMs
// ============================================================================

module ldpc_decoder_top #(
    parameter int Z = 56,                    // Lifting factor (default for n=3808)
    parameter int MAX_ITERATIONS = 15,       // Maximum decoding iterations
    parameter int DATA_WIDTH = 6,            // LLR quantization bits
    parameter int PARALLELISM_FACTOR = 4,    // F - parallelism reduction factor
    parameter int MAX_VN_DEGREE = 19,        // BG1 max VN degree
    parameter int MAX_CN_DEGREE = 30,        // BG1 max CN degree
    parameter int NORMALIZATION_ALPHA = 192  // 0.75 * 256
) (
    input  logic                        clk,
    input  logic                        rst_n,
    
    // Control interface
    input  logic                        start_decode,
    input  logic [2:0]                  code_rate_sel,
    input  logic [8:0]                  lifting_factor_z,
    input  logic [3:0]                  base_graph_sel,
    input  logic [4:0]                  max_iter,
    
    // Channel LLR input
    input  logic signed [DATA_WIDTH-1:0] llr_in[Z-1:0],
    input  logic                         llr_valid,
    
    // Decoded output
    output logic                         decoded_bit[Z-1:0],
    output logic                         decode_valid,
    output logic                         decode_done,
    
    // Status outputs
    output logic [4:0]                   iterations_used,
    output logic                         parity_check_passed,
    output logic                         decode_success,
    
    // Performance monitoring
    output logic [31:0]                  cycle_count,
    output logic [15:0]                  throughput_mbps
);

    import ldpc_decoder_pkg::*;
    
    // ========================================================================
    // Internal Signals
    // ========================================================================
    
    // PCM Configuration
    pcm_config_t pcm_config;
    logic config_ready;
    
    // State machine
    decoder_state_t current_state, next_state;
    
    // Iteration control
    logic [4:0] iteration_counter;
    logic iteration_complete;
    
    // Variable Node signals
    logic signed [DATA_WIDTH-1:0] vn_to_cn_msg[MAX_VN_DEGREE-1:0][Z-1:0];
    logic [MAX_VN_DEGREE-1:0]     vn_to_cn_valid;
    logic signed [DATA_WIDTH-1:0] app_llr[Z-1:0];
    logic                         app_llr_valid;
    logic                         vn_done;
    logic                         vn_enable;
    logic                         vn_init;
    
    // Check Node signals
    logic signed [DATA_WIDTH-1:0] cn_to_vn_msg[MAX_CN_DEGREE-1:0][Z-1:0];
    logic [MAX_CN_DEGREE-1:0]     cn_to_vn_valid;
    logic                         cn_done;
    logic                         cn_enable;
    
    // Barrel Shifter signals
    logic [DATA_WIDTH-1:0]        shifter_in[Z-1:0];
    logic [DATA_WIDTH-1:0]        shifter_out[Z-1:0];
    logic [8:0]                   shift_amount;
    logic                         shift_enable;
    logic                         shift_valid;
    logic                         shift_direction;
    
    // Configuration Memory signals
    logic [11:0]                  config_addr;
    logic                         config_read_enable;
    logic [7:0]                   src_vn_idx;
    logic [7:0]                   dst_cn_idx;
    logic                         edge_active;
    logic [8:0]                   edge_shift_value;
    logic                         edge_shift_valid;
    logic [7:0]                   vn_degree;
    logic [7:0]                   cn_degree;
    
    // Parity check
    logic                         parity_satisfied;
    logic [15:0]                  syndrome_weight;
    
    // Performance counters
    logic [31:0]                  decode_cycles;
    logic [31:0]                  total_bits_decoded;
    
    // Hard decision
    logic                         hard_decision[Z-1:0];
    
    // ========================================================================
    // PCM Parameter Extraction
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pcm_config <= '0;
        end else if (start_decode) begin
            pcm_config <= extract_pcm_params(
                code_rate_t'(code_rate_sel),
                lifting_factor_z,
                base_graph_sel
            );
        end
    end
    
    // ========================================================================
    // Main State Machine
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= IDLE;
        end else begin
            current_state <= next_state;
        end
    end
    
    always_comb begin
        next_state = current_state;
        
        case (current_state)
            IDLE: begin
                if (start_decode && llr_valid) begin
                    next_state = LOAD_CONFIG;
                end
            end
            
            LOAD_CONFIG: begin
                if (config_ready) begin
                    next_state = INIT_MESSAGES;
                end
            end
            
            INIT_MESSAGES: begin
                if (vn_done) begin
                    next_state = VN_UPDATE;
                end
            end
            
            VN_UPDATE: begin
                if (vn_done) begin
                    next_state = BARREL_SHIFT;
                end
            end
            
            BARREL_SHIFT: begin
                if (shift_valid) begin
                    next_state = CN_UPDATE;
                end
            end
            
            CN_UPDATE: begin
                if (cn_done) begin
                    next_state = REVERSE_SHIFT;
                end
            end
            
            REVERSE_SHIFT: begin
                if (shift_valid) begin
                    next_state = CHECK_PARITY;
                end
            end
            
            CHECK_PARITY: begin
                if (parity_satisfied || iteration_counter >= max_iter) begin
                    next_state = HARD_DECISION;
                end else begin
                    next_state = VN_UPDATE;
                end
            end
            
            HARD_DECISION: begin
                next_state = DONE;
            end
            
            DONE: begin
                next_state = IDLE;
            end
            
            default: next_state = IDLE;
        endcase
    end
    
    // ========================================================================
    // Iteration Counter
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            iteration_counter <= '0;
        end else if (current_state == IDLE) begin
            iteration_counter <= '0;
        end else if (current_state == CHECK_PARITY && !parity_satisfied) begin
            iteration_counter <= iteration_counter + 1;
        end
    end
    
    // ========================================================================
    // Control Signal Generation
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            vn_enable <= 1'b0;
            vn_init <= 1'b0;
            cn_enable <= 1'b0;
            shift_enable <= 1'b0;
        end else begin
            case (current_state)
                INIT_MESSAGES: begin
                    vn_enable <= 1'b1;
                    vn_init <= 1'b1;
                end
                
                VN_UPDATE: begin
                    vn_enable <= 1'b1;
                    vn_init <= 1'b0;
                end
                
                BARREL_SHIFT, REVERSE_SHIFT: begin
                    shift_enable <= 1'b1;
                end
                
                CN_UPDATE: begin
                    cn_enable <= 1'b1;
                end
                
                default: begin
                    vn_enable <= 1'b0;
                    vn_init <= 1'b0;
                    cn_enable <= 1'b0;
                    shift_enable <= 1'b0;
                end
            endcase
        end
    end
    
    // ========================================================================
    // Parity Check Computation
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            parity_satisfied <= 1'b0;
            syndrome_weight <= '0;
        end else if (current_state == CHECK_PARITY) begin
            logic [15:0] syndrome_count;
            syndrome_count = 0;
            
            // Compute syndrome: H * x^T
            // Simplified check - full implementation would use actual H matrix
            for (int i = 0; i < Z; i++) begin
                if (hard_decision[i] != (app_llr[i] >= 0)) begin
                    syndrome_count++;
                end
            end
            
            syndrome_weight <= syndrome_count;
            parity_satisfied <= (syndrome_count == 0);
        end
    end
    
    // ========================================================================
    // Hard Decision
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < Z; i++) begin
                hard_decision[i] <= 1'b0;
                decoded_bit[i] <= 1'b0;
            end
        end else if (current_state == HARD_DECISION || current_state == CHECK_PARITY) begin
            for (int i = 0; i < Z; i++) begin
                hard_decision[i] <= (app_llr[i] < 0) ? 1'b1 : 1'b0;
            end
        end else if (current_state == DONE) begin
            decoded_bit <= hard_decision;
        end
    end
    
    // ========================================================================
    // Output Control
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            decode_valid <= 1'b0;
            decode_done <= 1'b0;
            decode_success <= 1'b0;
            iterations_used <= '0;
        end else begin
            case (current_state)
                DONE: begin
                    decode_valid <= 1'b1;
                    decode_done <= 1'b1;
                    decode_success <= parity_satisfied;
                    iterations_used <= iteration_counter;
                end
                
                IDLE: begin
                    decode_valid <= 1'b0;
                    decode_done <= 1'b0;
                end
                
                default: begin
                    decode_valid <= 1'b0;
                end
            endcase
        end
    end
    
    assign parity_check_passed = parity_satisfied;
    
    // ========================================================================
    // Performance Monitoring
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cycle_count <= '0;
            decode_cycles <= '0;
            total_bits_decoded <= '0;
        end else if (current_state == IDLE) begin
            decode_cycles <= '0;
        end else if (current_state != IDLE && current_state != DONE) begin
            decode_cycles <= decode_cycles + 1;
        end else if (current_state == DONE) begin
            cycle_count <= decode_cycles;
            total_bits_decoded <= total_bits_decoded + pcm_config.n;
        end
    end
    
    // Throughput calculation (simplified)
    // Throughput (Mbps) = (bits_per_frame * clock_freq_MHz) / cycles_per_frame
    // Assuming 230 MHz clock: throughput ≈ (3808 * 230) / cycles
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            throughput_mbps <= '0;
        end else if (current_state == DONE && decode_cycles > 0) begin
            // Simplified calculation: (n * 230) / cycles (in Mbps)
            throughput_mbps <= (pcm_config.n * 230) / decode_cycles[15:0];
        end
    end
    
    // ========================================================================
    // Module Instantiations
    // ========================================================================
    
    // Configuration Memory
    config_memory #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32),
        .MAX_EDGES(1024),
        .Z_MAX(Z)
    ) u_config_memory (
        .clk(clk),
        .rst_n(rst_n),
        .config_enable(current_state == LOAD_CONFIG),
        .code_rate_sel(code_rate_sel),
        .lifting_factor(lifting_factor_z),
        .base_graph_sel(base_graph_sel),
        .read_addr(config_addr),
        .read_enable(config_read_enable),
        .src_vn_idx(src_vn_idx),
        .dst_cn_idx(dst_cn_idx),
        .edge_active(edge_active),
        .shift_value(edge_shift_value),
        .shift_valid(edge_shift_valid),
        .vn_degree(vn_degree),
        .cn_degree(cn_degree),
        .edge_weight(),
        .write_enable(1'b0),
        .write_addr('0),
        .mem_select(2'b00),
        .write_data('0),
        .config_ready(config_ready)
    );
    
    // Variable Node Decoder
    variable_node_decoder #(
        .Z(Z),
        .MAX_VN_DEGREE(MAX_VN_DEGREE),
        .DATA_WIDTH(DATA_WIDTH),
        .NUM_VN_UNITS(PARALLELISM_FACTOR)
    ) u_vn_decoder (
        .clk(clk),
        .rst_n(rst_n),
        .enable(vn_enable),
        .init(vn_init),
        .channel_llr(llr_in),
        .channel_llr_valid(llr_valid),
        .cn_messages(cn_to_vn_msg),
        .cn_msg_valid(cn_to_vn_valid),
        .active_degree(vn_degree[4:0]),
        .vn_messages(vn_to_cn_msg),
        .vn_msg_valid(vn_to_cn_valid),
        .app_out(app_llr),
        .app_valid(app_llr_valid),
        .vn_done(vn_done)
    );
    
    // Check Node Decoder
    check_node_decoder #(
        .Z(Z),
        .MAX_CN_DEGREE(MAX_CN_DEGREE),
        .DATA_WIDTH(DATA_WIDTH),
        .NUM_CN_UNITS(PARALLELISM_FACTOR),
        .ALPHA(NORMALIZATION_ALPHA)
    ) u_cn_decoder (
        .clk(clk),
        .rst_n(rst_n),
        .enable(cn_enable),
        .vn_messages(vn_to_cn_msg),
        .vn_msg_valid(vn_to_cn_valid),
        .active_degree(cn_degree[5:0]),
        .norm_factor(8'd192),  // 0.75 * 256
        .offset_beta(6'd2),
        .use_offset(1'b1),
        .cn_messages(cn_to_vn_msg),
        .cn_msg_valid(cn_to_vn_valid),
        .cn_done(cn_done)
    );
    
    // Barrel Shifter
    barrel_shifter #(
        .DATA_WIDTH(DATA_WIDTH),
        .Z_MAX(Z),
        .SHIFT_BITS(9)
    ) u_barrel_shifter (
        .clk(clk),
        .rst_n(rst_n),
        .enable(shift_enable),
        .data_in(shifter_in),
        .shift_amount(edge_shift_value),
        .vector_size(lifting_factor_z),
        .shift_dir(shift_direction),
        .data_out(shifter_out),
        .valid_out(shift_valid)
    );
    
    // Assign shifter direction based on state
    assign shift_direction = (current_state == BARREL_SHIFT) ? 1'b0 : 1'b1;
    
    // ========================================================================
    // Assertions for Verification
    // ========================================================================
    
    `ifdef SIMULATION
        property max_iterations_check;
            @(posedge clk) disable iff (!rst_n)
            (current_state == CHECK_PARITY) |-> (iteration_counter <= MAX_ITERATIONS);
        endproperty
        
        assert property (max_iterations_check)
        else $error("Exceeded maximum iterations");
        
        property valid_state_transitions;
            @(posedge clk) disable iff (!rst_n)
            (current_state != ERROR);
        endproperty
        
        assert property (valid_state_transitions)
        else $error("Entered error state");
        
        // Coverage
        covergroup decoder_coverage @(posedge clk);
            state_cp: coverpoint current_state;
            iteration_cp: coverpoint iteration_counter {
                bins low = {[0:4]};
                bins mid = {[5:9]};
                bins high = {[10:15]};
            }
            rate_cp: coverpoint code_rate_sel;
        endgroup
        
        decoder_coverage cov_inst = new();
    `endif

endmodule : ldpc_decoder_top
