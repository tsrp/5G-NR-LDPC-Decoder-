// ============================================================================
// Variable Node Decoder (VND)
// Implements variable node processing for LDPC decoding
// Uses normalized min-sum algorithm with message passing
// ============================================================================

module variable_node_decoder #(
    parameter int Z = 56,                    // Lifting factor
    parameter int MAX_VN_DEGREE = 19,        // Maximum variable node degree (BG1)
    parameter int DATA_WIDTH = 6,            // Message bit width
    parameter int NUM_VN_UNITS = 4           // Parallel VN processing units
) (
    input  logic                        clk,
    input  logic                        rst_n,
    input  logic                        enable,
    input  logic                        init,
    
    // Channel LLR inputs
    input  logic signed [DATA_WIDTH-1:0] channel_llr[Z-1:0],
    input  logic                         channel_llr_valid,
    
    // Messages from Check Nodes
    input  logic signed [DATA_WIDTH-1:0] cn_messages[MAX_VN_DEGREE-1:0][Z-1:0],
    input  logic [MAX_VN_DEGREE-1:0]     cn_msg_valid,
    input  logic [4:0]                   active_degree,  // Current node degree
    
    // Messages to Check Nodes
    output logic signed [DATA_WIDTH-1:0] vn_messages[MAX_VN_DEGREE-1:0][Z-1:0],
    output logic [MAX_VN_DEGREE-1:0]     vn_msg_valid,
    
    // APP (A Posteriori Probability) output for hard decision
    output logic signed [DATA_WIDTH-1:0] app_out[Z-1:0],
    output logic                         app_valid,
    
    // Status
    output logic                         vn_done
);

    import ldpc_decoder_pkg::*;
    
    // Internal registers
    logic signed [DATA_WIDTH-1:0] llr_memory[Z-1:0];
    logic signed [DATA_WIDTH-1:0] msg_memory[MAX_VN_DEGREE-1:0][Z-1:0];
    logic signed [DATA_WIDTH-1:0] sum_messages[Z-1:0];
    
    // Control signals
    logic [4:0] processing_edge;
    logic processing_active;
    
    typedef enum logic [2:0] {
        VN_IDLE,
        VN_INIT,
        VN_ACCUMULATE,
        VN_COMPUTE,
        VN_OUTPUT,
        VN_DONE
    } vn_state_t;
    
    vn_state_t state, next_state;
    
    // ========================================================================
    // State Machine
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= VN_IDLE;
        end else begin
            state <= next_state;
        end
    end
    
    always_comb begin
        next_state = state;
        
        case (state)
            VN_IDLE: begin
                if (enable && init) begin
                    next_state = VN_INIT;
                end else if (enable) begin
                    next_state = VN_ACCUMULATE;
                end
            end
            
            VN_INIT: begin
                next_state = VN_DONE;
            end
            
            VN_ACCUMULATE: begin
                if (processing_edge >= active_degree) begin
                    next_state = VN_COMPUTE;
                end
            end
            
            VN_COMPUTE: begin
                next_state = VN_OUTPUT;
            end
            
            VN_OUTPUT: begin
                next_state = VN_DONE;
            end
            
            VN_DONE: begin
                next_state = VN_IDLE;
            end
            
            default: next_state = VN_IDLE;
        endcase
    end
    
    // ========================================================================
    // Initialization: Store channel LLRs
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < Z; i++) begin
                llr_memory[i] <= '0;
            end
        end else if (state == VN_INIT && channel_llr_valid) begin
            llr_memory <= channel_llr;
        end
    end
    
    // ========================================================================
    // Message Update: VN Processing
    // Variable node update rule: 
    // vn_msg[j] = channel_llr + sum(cn_messages[i]) - cn_messages[j]
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            processing_edge <= '0;
            processing_active <= 1'b0;
            
            for (int i = 0; i < MAX_VN_DEGREE; i++) begin
                for (int j = 0; j < Z; j++) begin
                    msg_memory[i][j] <= '0;
                end
            end
        end else begin
            case (state)
                VN_IDLE: begin
                    processing_edge <= '0;
                    processing_active <= 1'b0;
                end
                
                VN_ACCUMULATE: begin
                    if (cn_msg_valid[processing_edge]) begin
                        // Store incoming CN messages
                        msg_memory[processing_edge] <= cn_messages[processing_edge];
                    end
                    processing_edge <= processing_edge + 1;
                end
                
                VN_COMPUTE: begin
                    processing_active <= 1'b1;
                    
                    // Compute total sum for each Z element
                    for (int z_idx = 0; z_idx < Z; z_idx++) begin
                        logic signed [DATA_WIDTH+4:0] total_sum;
                        total_sum = llr_memory[z_idx];
                        
                        for (int edge = 0; edge < MAX_VN_DEGREE; edge++) begin
                            if (edge < active_degree) begin
                                total_sum = total_sum + msg_memory[edge][z_idx];
                            end
                        end
                        
                        sum_messages[z_idx] <= saturate_add(
                            llr_memory[z_idx],
                            total_sum[DATA_WIDTH-1:0]
                        );
                    end
                end
                
                VN_OUTPUT: begin
                    // Compute outgoing messages: total_sum - incoming_msg[j]
                    for (int edge = 0; edge < MAX_VN_DEGREE; edge++) begin
                        if (edge < active_degree) begin
                            for (int z_idx = 0; z_idx < Z; z_idx++) begin
                                vn_messages[edge][z_idx] <= saturate_add(
                                    sum_messages[z_idx],
                                    -msg_memory[edge][z_idx]
                                );
                            end
                        end
                    end
                    
                    // APP output is the total sum
                    app_out <= sum_messages;
                end
                
                default: begin
                    processing_active <= 1'b0;
                end
            endcase
        end
    end
    
    // ========================================================================
    // Output Control
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            vn_msg_valid <= '0;
            app_valid <= 1'b0;
            vn_done <= 1'b0;
        end else begin
            case (state)
                VN_OUTPUT: begin
                    for (int i = 0; i < MAX_VN_DEGREE; i++) begin
                        vn_msg_valid[i] <= (i < active_degree);
                    end
                    app_valid <= 1'b1;
                end
                
                VN_DONE: begin
                    vn_done <= 1'b1;
                    vn_msg_valid <= '0;
                    app_valid <= 1'b0;
                end
                
                default: begin
                    vn_msg_valid <= '0;
                    app_valid <= 1'b0;
                    vn_done <= 1'b0;
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
            enable |-> (active_degree <= MAX_VN_DEGREE);
        endproperty
        
        assert property (valid_degree)
        else $error("VN degree exceeds maximum");
    `endif

endmodule : variable_node_decoder
