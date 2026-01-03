// ============================================================================
// Configuration Memory Subsystem
// Three-memory architecture: LOCATION, ADJUST, and STATUS
// Enables runtime reconfiguration for multiple code rates
// ============================================================================

module config_memory #(
    parameter int ADDR_WIDTH = 12,
    parameter int DATA_WIDTH = 32,
    parameter int MAX_EDGES = 1024,      // Maximum edges in base graph
    parameter int Z_MAX = 384
) (
    input  logic                        clk,
    input  logic                        rst_n,
    
    // Configuration interface
    input  logic                        config_enable,
    input  logic [2:0]                  code_rate_sel,
    input  logic [8:0]                  lifting_factor,
    input  logic [3:0]                  base_graph_sel,
    
    // Read interface for decoder
    input  logic [ADDR_WIDTH-1:0]      read_addr,
    input  logic                        read_enable,
    
    // LOCATION memory outputs (edge connectivity)
    output logic [7:0]                  src_vn_idx,
    output logic [7:0]                  dst_cn_idx,
    output logic                        edge_active,
    
    // ADJUST memory outputs (shift values)
    output logic [8:0]                  shift_value,
    output logic                        shift_valid,
    
    // STATUS memory outputs (weights and metadata)
    output logic [7:0]                  vn_degree,
    output logic [7:0]                  cn_degree,
    output logic [15:0]                 edge_weight,
    
    // Write interface for configuration loading
    input  logic                        write_enable,
    input  logic [ADDR_WIDTH-1:0]      write_addr,
    input  logic [1:0]                  mem_select,  // 0=LOCATION, 1=ADJUST, 2=STATUS
    input  logic [DATA_WIDTH-1:0]      write_data,
    
    // Status
    output logic                        config_ready
);

    import ldpc_decoder_pkg::*;
    
    // ========================================================================
    // Memory Definitions
    // ========================================================================
    
    // LOCATION Memory: Stores edge connectivity information
    // Format: {dst_cn_idx[15:8], src_vn_idx[7:0], edge_active[0]}
    logic [23:0] location_mem[MAX_EDGES-1:0];
    
    // ADJUST Memory: Stores cyclic shift values
    // Format: {shift_value[8:0], shift_valid[0]}
    logic [9:0] adjust_mem[MAX_EDGES-1:0];
    
    // STATUS Memory: Stores node degrees and weights
    // Format: {edge_weight[31:16], cn_degree[15:8], vn_degree[7:0]}
    logic [31:0] status_mem[MAX_EDGES-1:0];
    
    // Configuration registers
    logic [2:0]  current_rate;
    logic [8:0]  current_z;
    logic [3:0]  current_bg;
    logic        config_loaded;
    
    // Read pipeline registers
    logic [23:0] location_read_data;
    logic [9:0]  adjust_read_data;
    logic [31:0] status_read_data;
    
    // ========================================================================
    // Configuration Control
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_rate <= 3'b000;
            current_z <= 9'd56;
            current_bg <= 4'd1;
            config_loaded <= 1'b0;
            config_ready <= 1'b0;
        end else if (config_enable) begin
            current_rate <= code_rate_sel;
            current_z <= lifting_factor;
            current_bg <= base_graph_sel;
            config_loaded <= 1'b1;
            config_ready <= 1'b1;
        end
    end
    
    // ========================================================================
    // Memory Write Operations
    // ========================================================================
    
    always_ff @(posedge clk) begin
        if (write_enable) begin
            case (mem_select)
                2'b00: begin  // LOCATION memory
                    location_mem[write_addr] <= write_data[23:0];
                end
                
                2'b01: begin  // ADJUST memory
                    adjust_mem[write_addr] <= write_data[9:0];
                end
                
                2'b10: begin  // STATUS memory
                    status_mem[write_addr] <= write_data;
                end
                
                default: begin
                    // No operation
                end
            endcase
        end
    end
    
    // ========================================================================
    // Memory Read Operations (Pipelined)
    // ========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            location_read_data <= '0;
            adjust_read_data <= '0;
            status_read_data <= '0;
        end else if (read_enable) begin
            location_read_data <= location_mem[read_addr];
            adjust_read_data <= adjust_mem[read_addr];
            status_read_data <= status_mem[read_addr];
        end
    end
    
    // ========================================================================
    // Output Assignment
    // ========================================================================
    
    always_comb begin
        // LOCATION memory outputs
        src_vn_idx = location_read_data[7:0];
        dst_cn_idx = location_read_data[15:8];
        edge_active = location_read_data[0];
        
        // ADJUST memory outputs
        shift_value = adjust_read_data[9:1];
        shift_valid = adjust_read_data[0];
        
        // STATUS memory outputs
        vn_degree = status_read_data[7:0];
        cn_degree = status_read_data[15:8];
        edge_weight = status_read_data[31:16];
    end
    
    // ========================================================================
    // Initialization with 5G NR BG1 Default Configuration
    // Example for BG1, Rate 1/3, Z=56
    // ========================================================================
    
    initial begin
        // Initialize all memories to zero
        for (int i = 0; i < MAX_EDGES; i++) begin
            location_mem[i] = '0;
            adjust_mem[i] = '0;
            status_mem[i] = '0;
        end
        
        // Load default BG1 configuration
        // This is a simplified example - full configuration would be loaded
        // from external source or ROM
        
        // Example edges for BG1 (first few entries)
        // Edge 0: VN=0, CN=0, shift=0
        location_mem[0] = 24'h000001;  // CN=0, VN=0, active=1
        adjust_mem[0] = 10'h001;       // shift=0, valid=1
        status_mem[0] = 32'h00010303;  // weight=1, cn_deg=3, vn_deg=3
        
        // Edge 1: VN=1, CN=0, shift=0
        location_mem[1] = 24'h000101;
        adjust_mem[1] = 10'h001;
        status_mem[1] = 32'h00010303;
        
        // Edge 2: VN=2, CN=0, shift=1
        location_mem[2] = 24'h000201;
        adjust_mem[2] = 10'h003;       // shift=1, valid=1
        status_mem[2] = 32'h00010303;
        
        // Additional edges would be initialized here...
        // In practice, this would be loaded from a file or ROM
    end
    
    // ========================================================================
    // Runtime Reconfiguration Support
    // ========================================================================
    
    // Function to enable/disable edges based on code rate
    function automatic logic is_edge_active_for_rate(
        input logic [2:0] rate,
        input logic [ADDR_WIDTH-1:0] edge_idx,
        input logic [3:0] bg_type
    );
        logic active;
        
        // Simplified logic - in practice, this would use lookup tables
        // Higher code rates use fewer parity check equations
        case (rate)
            3'b000: active = 1'b1;  // Rate 1/3 - all edges active
            3'b001: active = (edge_idx < 768);  // Rate 1/2
            3'b010: active = (edge_idx < 512);  // Rate 2/3
            3'b011: active = (edge_idx < 384);  // Rate 3/4
            3'b100: active = (edge_idx < 256);  // Rate 5/6
            3'b101: active = (edge_idx < 128);  // Rate 8/9
            default: active = 1'b0;
        endcase
        
        return active;
    endfunction
    
    // ========================================================================
    // Assertions
    // ========================================================================
    
    `ifdef SIMULATION
        property valid_mem_select;
            @(posedge clk) disable iff (!rst_n)
            write_enable |-> (mem_select <= 2'b10);
        endproperty
        
        assert property (valid_mem_select)
        else $error("Invalid memory select value");
        
        property valid_lifting_factor;
            @(posedge clk) disable iff (!rst_n)
            config_enable |-> (lifting_factor >= Z_MIN && lifting_factor <= Z_MAX);
        endproperty
        
        assert property (valid_lifting_factor)
        else $error("Invalid lifting factor");
    `endif

endmodule : config_memory
