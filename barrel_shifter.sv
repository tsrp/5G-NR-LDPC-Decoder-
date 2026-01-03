// ============================================================================
// Programmable Barrel Shifter for Cyclic Message Alignment
// Implements efficient cyclic shifts for QC-LDPC decoder
// ============================================================================

module barrel_shifter #(
    parameter int DATA_WIDTH = 6,      // Message width
    parameter int Z_MAX = 384,         // Maximum lifting factor
    parameter int SHIFT_BITS = 9       // log2(Z_MAX)
) (
    input  logic                        clk,
    input  logic                        rst_n,
    input  logic                        enable,
    
    // Input data vector
    input  logic [DATA_WIDTH-1:0]      data_in[Z_MAX-1:0],
    input  logic [SHIFT_BITS-1:0]      shift_amount,
    input  logic [SHIFT_BITS-1:0]      vector_size,  // Actual Z value
    input  logic                        shift_dir,     // 0=right, 1=left
    
    // Output data vector
    output logic [DATA_WIDTH-1:0]      data_out[Z_MAX-1:0],
    output logic                        valid_out
);

    import ldpc_decoder_pkg::*;
    
    // Internal signals
    logic [DATA_WIDTH-1:0] shifted_data[Z_MAX-1:0];
    logic [SHIFT_BITS-1:0] effective_shift;
    
    // Pipeline registers
    logic [DATA_WIDTH-1:0] stage1[Z_MAX-1:0];
    logic [DATA_WIDTH-1:0] stage2[Z_MAX-1:0];
    logic valid_stage1, valid_stage2;
    
    // Calculate effective shift (modulo vector_size)
    always_comb begin
        effective_shift = shift_amount % vector_size;
    end
    
    // Multi-stage barrel shifter for better timing
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < Z_MAX; i++) begin
                stage1[i] <= '0;
                stage2[i] <= '0;
                data_out[i] <= '0;
            end
            valid_stage1 <= 1'b0;
            valid_stage2 <= 1'b0;
            valid_out <= 1'b0;
        end else if (enable) begin
            // Stage 1: Coarse shift (multiples of 16)
            for (int i = 0; i < Z_MAX; i++) begin
                if (shift_dir == 1'b0) begin  // Right shift
                    stage1[i] <= data_in[(i + (effective_shift & 9'h1F0)) % vector_size];
                end else begin  // Left shift
                    stage1[i] <= data_in[(i - (effective_shift & 9'h1F0) + vector_size) % vector_size];
                end
            end
            valid_stage1 <= 1'b1;
            
            // Stage 2: Fine shift (remaining bits)
            for (int i = 0; i < Z_MAX; i++) begin
                if (shift_dir == 1'b0) begin  // Right shift
                    stage2[i] <= stage1[(i + (effective_shift & 9'h00F)) % vector_size];
                end else begin  // Left shift
                    stage2[i] <= stage1[(i - (effective_shift & 9'h00F) + vector_size) % vector_size];
                end
            end
            valid_stage2 <= valid_stage1;
            
            // Output stage
            data_out <= stage2;
            valid_out <= valid_stage2;
        end else begin
            valid_out <= 1'b0;
        end
    end
    
    // Assertions for verification
    `ifdef SIMULATION
        property shift_range_check;
            @(posedge clk) disable iff (!rst_n)
            enable |-> (shift_amount < vector_size);
        endproperty
        
        assert property (shift_range_check)
        else $error("Shift amount exceeds vector size");
        
        property vector_size_check;
            @(posedge clk) disable iff (!rst_n)
            enable |-> (vector_size <= Z_MAX && vector_size > 0);
        endproperty
        
        assert property (vector_size_check)
        else $error("Invalid vector size");
    `endif

endmodule : barrel_shifter
