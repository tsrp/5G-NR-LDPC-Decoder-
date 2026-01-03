// ============================================================================
// Check Node Decoder (CND)
// Implements check node processing using Normalized Min-Sum algorithm
// Optimized for 5G NR LDPC codes
// ============================================================================

module check_node_decoder #(
    parameter int Z = 56,                    // Lifting factor
    parameter int MAX_CN_DEGREE = 30,        // Maximum check node degree (BG1)
    parameter int DATA_WIDTH = 6,            // Message bit width
    parameter int NUM_CN_UNITS = 4,          // Parallel CN processing units
    parameter int ALPHA = 192                // Normalization factor (0.75*256)
) (
    input  logic                        clk,
    input  logic                        rst_n,
    input  logic                        enable,
    
    // Messages from Variable Nodes
    input  logic signed [DATA_WIDTH-1:0] vn_messages[MAX_CN_DEGREE-1:0][Z-1:0],
    input  logic [MAX_CN_DEGREE-1:0]     vn_msg_valid,
    input  logic [5:0]                   active_degree,  // Current node degree
    
    // Normalization control
    input  logic [7:0]                   norm_factor,    // Alpha for NMS
    input  logic [DATA_WIDTH-1:0]        offset_beta,    // Beta for OMS
    input  logic                         use_offset,     // Enable offset min-sum
    
    // Messages to Variable Nodes
    output logic signed [DATA_WIDTH-1:0] cn_messages[MAX_CN_DEGREE-1:0][Z-1:0],
    output logic [MAX_CN_DEGREE-1:0]     cn_msg_valid,
    
    // Status
    output logic                         cn_done
);

    import ldpc_decoder_pkg::*;
    
    // Internal storage
    logic signed [DATA_WIDTH-1:0] msg_memory[MAX_CN_DEGREE-1:0][Z-1:0];
    logic signed [DATA_WIDTH-1:0] min1[Z-1:0];      // First minimum
    logic signed [DATA_WIDTH-1:0] min2[Z-1:0];      // Second minimum
    logic [5:0]                   min1_idx[Z-1:0];  // Index of first minimum
    logic                         sign_product[Z-1:0];
    
    // State machine
    typedef enum logic [2:0] {
        CN_IDLE,
        CN_LOAD,
        CN_FIND_MIN,
        CN_COMPUTE,
        CN_OUTPUT,
        CN_DONE
    } cn_state_t;
    
    cn_state_t state, next_state;
    
    logic [5:0] load_counter;
    logic [5:0] compute_counter;
    
    // ========================================================================
    // State Machine
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= CN_IDLE;
        end else begin
            state <= next_state;
        end
    end
    
    always_comb begin
        next_state = state;
        
        case (state)
            CN_IDLE: begin
                if (enable) begin
                    next_state = CN_LOAD;
                end
            end
            
            CN_LOAD: begin
                if (load_counter >= active_degree) begin
                    next_state = CN_FIND_MIN;
                end
            end
            
            CN_FIND_MIN: begin
                next_state = CN_COMPUTE;
            end
            
            CN_COMPUTE: begin
                if (compute_counter >= active_degree) begin
                    next_state = CN_OUTPUT;
                end
            end
            
            CN_OUTPUT: begin
                next_state = CN_DONE;
            end
            
            CN_DONE: begin
                next_state = CN_IDLE;
            end
            
            default: next_state = CN_IDLE;
        endcase
    end
    
    // ========================================================================
    // Load incoming messages
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            load_counter <= '0;
            for (int i = 0; i < MAX_CN_DEGREE; i++) begin
                for (int j = 0; j < Z; j++) begin
                    msg_memory[i][j] <= '0;
                end
            end
        end else if (state == CN_IDLE) begin
            load_counter <= '0;
        end else if (state == CN_LOAD) begin
            if (vn_msg_valid[load_counter]) begin
                msg_memory[load_counter] <= vn_messages[load_counter];
            end
            load_counter <= load_counter + 1;
        end
    end
    
    // ========================================================================
    // Find two minimum values and compute sign product
    // Normalized Min-Sum Algorithm
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < Z; i++) begin
                min1[i] <= '1;  // Initialize to max positive
                min2[i] <= '1;
                min1_idx[i] <= '0;
                sign_product[i] <= 1'b0;
            end
        end else if (state == CN_FIND_MIN) begin
            // Process each Z element in parallel
            for (int z_idx = 0; z_idx < Z; z_idx++) begin
                logic signed [DATA_WIDTH-1:0] abs_values[MAX_CN_DEGREE-1:0];
                logic signed [DATA_WIDTH-1:0] local_min1, local_min2;
                logic [5:0] local_min1_idx;
                logic local_sign;
                
                // Initialize
                local_min1 = {1'b0, {(DATA_WIDTH-1){1'b1}}};  // Max positive
                local_min2 = {1'b0, {(DATA_WIDTH-1){1'b1}}};
                local_min1_idx = 0;
                local_sign = 1'b0;
                
                // Find minimums and sign product
                for (int edge = 0; edge < MAX_CN_DEGREE; edge++) begin
                    if (edge < active_degree) begin
                        logic signed [DATA_WIDTH-1:0] abs_val;
                        logic msg_sign;
                        
                        // Get absolute value and sign
                        msg_sign = msg_memory[edge][z_idx][DATA_WIDTH-1];
                        abs_val = msg_sign ? -msg_memory[edge][z_idx] : msg_memory[edge][z_idx];
                        
                        // Update sign product
                        local_sign = local_sign ^ msg_sign;
                        
                        // Update minimums
                        if (abs_val < local_min1) begin
                            local_min2 = local_min1;
                            local_min1 = abs_val;
                            local_min1_idx = edge[5:0];
                        end else if (abs_val < local_min2) begin
                            local_min2 = abs_val;
                        end
                    end
                end
                
                min1[z_idx] <= local_min1;
                min2[z_idx] <= local_min2;
                min1_idx[z_idx] <= local_min1_idx;
                sign_product[z_idx] <= local_sign;
            end
        end
    end
    
    // ========================================================================
    // Compute outgoing messages
    // CN update rule: cn_msg[j] = sign * min_value
    // where min_value = min2 if j==min1_idx, else min1
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            compute_counter <= '0;
            for (int i = 0; i < MAX_CN_DEGREE; i++) begin
                for (int j = 0; j < Z; j++) begin
                    cn_messages[i][j] <= '0;
                end
            end
        end else if (state == CN_IDLE) begin
            compute_counter <= '0;
        end else if (state == CN_COMPUTE) begin
            for (int edge = 0; edge < MAX_CN_DEGREE; edge++) begin
                if (edge < active_degree) begin
                    for (int z_idx = 0; z_idx < Z; z_idx++) begin
                        logic signed [DATA_WIDTH-1:0] min_val, normalized_val;
                        logic msg_sign, result_sign;
                        
                        // Select appropriate minimum
                        min_val = (edge == min1_idx[z_idx]) ? min2[z_idx] : min1[z_idx];
                        
                        // Apply normalization
                        normalized_val = apply_normalization(min_val, norm_factor);
                        
                        // Apply offset if enabled
                        if (use_offset) begin
                            normalized_val = apply_offset(normalized_val, offset_beta);
                        end
                        
                        // Compute output sign
                        msg_sign = msg_memory[edge][z_idx][DATA_WIDTH-1];
                        result_sign = sign_product[z_idx] ^ msg_sign;
                        
                        // Assign final message
                        cn_messages[edge][z_idx] <= result_sign ? -normalized_val : normalized_val;
                    end
                end
            end
            compute_counter <= compute_counter + 1;
        end
    end
    
    // ========================================================================
    // Output Control
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cn_msg_valid <= '0;
            cn_done <= 1'b0;
        end else begin
            case (state)
                CN_OUTPUT: begin
                    for (int i = 0; i < MAX_CN_DEGREE; i++) begin
                        cn_msg_valid[i] <= (i < active_degree);
                    end
                end
                
                CN_DONE: begin
                    cn_done <= 1'b1;
                    cn_msg_valid <= '0;
                end
                
                default: begin
                    cn_msg_valid <= '0;
                    cn_done <= 1'b0;
                end
            endcase
        end
    end
    
    // ========================================================================
    // Assertions
    // ========================================================================
    
    `ifdef SIMULATION
        property valid_degree;
            @(posedge clk) disable iff (!rst_n)
            enable |-> (active_degree <= MAX_CN_DEGREE);
        endproperty
        
        assert property (valid_degree)
        else $error("CN degree exceeds maximum");
        
        property normalization_range;
            @(posedge clk) disable iff (!rst_n)
            enable |-> (norm_factor > 0 && norm_factor <= 256);
        endproperty
        
        assert property (normalization_range)
        else $warning("Normalization factor out of typical range");
    `endif

endmodule : check_node_decoder
