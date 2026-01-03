// ============================================================================
// 5G NR LDPC Decoder Package
// Package containing parameters, types, and functions for 5G NR LDPC decoder
// ============================================================================

package ldpc_decoder_pkg;

    // ========================================================================
    // Global Parameters for 5G NR LDPC
    // ========================================================================
    
    // Base Graph Selection (BG1 or BG2)
    parameter int BG_TYPE = 1;  // 1 for BG1, 2 for BG2
    
    // BG1 Parameters (for eMBB high throughput)
    parameter int BG1_MB = 68;  // Number of rows in base graph 1
    parameter int BG1_NB = 22;  // Number of columns in base graph 1
    parameter int BG1_KB = 22;  // Information columns
    
    // BG2 Parameters (for IoT/URLLC)
    parameter int BG2_MB = 42;  // Number of rows in base graph 2
    parameter int BG2_NB = 10;  // Number of columns in base graph 2
    parameter int BG2_KB = 10;  // Information columns
    
    // Lifting factor Z (expansion factor)
    parameter int Z_MIN = 2;
    parameter int Z_MAX = 384;
    parameter int Z_DEFAULT = 56;  // Example for n=3808 (68*56)
    
    // Decoder Configuration
    parameter int MAX_ITERATIONS = 15;      // Maximum decoding iterations
    parameter int QUANTIZATION_BITS = 6;    // LLR quantization bits
    parameter int PARALLELISM_FACTOR = 4;   // F - parallelism reduction factor
    
    // Message bit widths
    parameter int LLR_WIDTH = QUANTIZATION_BITS;
    parameter int MSG_WIDTH = QUANTIZATION_BITS;
    
    // Memory addressing
    parameter int ADDR_WIDTH = 12;
    
    // Code rates supported (5G NR eMBB)
    typedef enum logic [2:0] {
        RATE_1_3  = 3'b000,  // R = 1/3
        RATE_1_2  = 3'b001,  // R = 1/2
        RATE_2_3  = 3'b010,  // R = 2/3
        RATE_3_4  = 3'b011,  // R = 3/4
        RATE_5_6  = 3'b100,  // R = 5/6
        RATE_8_9  = 3'b101   // R = 8/9
    } code_rate_t;
    
    // Decoder states
    typedef enum logic [3:0] {
        IDLE           = 4'b0000,
        LOAD_CONFIG    = 4'b0001,
        INIT_MESSAGES  = 4'b0010,
        VN_UPDATE      = 4'b0011,
        BARREL_SHIFT   = 4'b0100,
        CN_UPDATE      = 4'b0101,
        REVERSE_SHIFT  = 4'b0110,
        CHECK_PARITY   = 4'b0111,
        HARD_DECISION  = 4'b1000,
        DONE           = 4'b1001,
        ERROR          = 4'b1010
    } decoder_state_t;
    
    // ========================================================================
    // Data Structures
    // ========================================================================
    
    // PCM Configuration Structure
    typedef struct packed {
        logic [15:0] n;              // Codeword length
        logic [15:0] k;              // Information bits
        logic [15:0] m;              // Parity bits (n-k)
        logic [7:0]  mb;             // Base graph rows
        logic [7:0]  nb;             // Base graph columns
        logic [7:0]  kb;             // Information columns
        logic [8:0]  z;              // Lifting factor
        code_rate_t  rate;           // Code rate
        logic [3:0]  bg_type;        // Base graph type (1 or 2)
        logic        valid;          // Configuration valid flag
    } pcm_config_t;
    
    // Message structure for VN-CN communication
    typedef struct packed {
        logic signed [MSG_WIDTH-1:0] data;
        logic                        valid;
        logic [ADDR_WIDTH-1:0]      addr;
    } message_t;
    
    // Status memory entry
    typedef struct packed {
        logic [7:0]  row_weight;     // Number of 1s in the row
        logic [7:0]  col_weight;     // Number of 1s in the column
        logic [15:0] shift_value;    // Cyclic shift value
        logic        is_active;      // Active in current code rate
    } status_entry_t;
    
    // ========================================================================
    // Functions
    // ========================================================================
    
    // Min-Sum algorithm: Find minimum
    function automatic logic signed [MSG_WIDTH-1:0] min_value(
        input logic signed [MSG_WIDTH-1:0] a,
        input logic signed [MSG_WIDTH-1:0] b
    );
        return (a < b) ? a : b;
    endfunction
    
    // Min-Sum algorithm: Find sign
    function automatic logic sign_product(
        input logic signed [MSG_WIDTH-1:0] values[],
        input int num_values
    );
        logic sign;
        sign = 0;
        for (int i = 0; i < num_values; i++) begin
            sign ^= values[i][MSG_WIDTH-1];
        end
        return sign;
    endfunction
    
    // Saturation addition
    function automatic logic signed [MSG_WIDTH-1:0] saturate_add(
        input logic signed [MSG_WIDTH-1:0] a,
        input logic signed [MSG_WIDTH-1:0] b
    );
        logic signed [MSG_WIDTH:0] temp;
        logic signed [MSG_WIDTH-1:0] result;
        
        temp = a + b;
        
        // Check for overflow
        if (temp > $signed({1'b0, {(MSG_WIDTH-1){1'b1}}})) begin
            result = {1'b0, {(MSG_WIDTH-1){1'b1}}};  // Max positive
        end else if (temp < $signed({1'b1, {(MSG_WIDTH-1){1'b0}}})) begin
            result = {1'b1, {(MSG_WIDTH-1){1'b0}}};  // Max negative
        end else begin
            result = temp[MSG_WIDTH-1:0];
        end
        
        return result;
    endfunction
    
    // Calculate frame length from code rate and Z
    function automatic int calculate_frame_length(
        input code_rate_t rate,
        input int z,
        input int bg_type
    );
        int nb;
        nb = (bg_type == 1) ? BG1_NB : BG2_NB;
        return nb * z;
    endfunction
    
    // Extract PCM parameters
    function automatic pcm_config_t extract_pcm_params(
        input code_rate_t rate,
        input int z,
        input int bg_type
    );
        pcm_config_t config;
        
        config.bg_type = bg_type;
        config.rate = rate;
        config.z = z;
        
        if (bg_type == 1) begin
            config.mb = BG1_MB;
            config.nb = BG1_NB;
            config.kb = BG1_KB;
        end else begin
            config.mb = BG2_MB;
            config.nb = BG2_NB;
            config.kb = BG2_KB;
        end
        
        config.n = config.nb * z;
        
        // Calculate k based on code rate
        case (rate)
            RATE_1_3: config.k = config.n / 3;
            RATE_1_2: config.k = config.n / 2;
            RATE_2_3: config.k = (config.n * 2) / 3;
            RATE_3_4: config.k = (config.n * 3) / 4;
            RATE_5_6: config.k = (config.n * 5) / 6;
            RATE_8_9: config.k = (config.n * 8) / 9;
            default:  config.k = config.n / 3;
        endcase
        
        config.m = config.n - config.k;
        config.valid = 1'b1;
        
        return config;
    endfunction
    
    // Normalization factor for Normalized Min-Sum
    function automatic logic signed [MSG_WIDTH-1:0] apply_normalization(
        input logic signed [MSG_WIDTH-1:0] value,
        input logic [7:0] alpha  // Normalization factor (typically 0.75 * 256)
    );
        logic signed [MSG_WIDTH+7:0] temp;
        temp = value * $signed({1'b0, alpha});
        return temp[MSG_WIDTH+7:8];  // Divide by 256
    endfunction
    
    // Offset Min-Sum offset application
    function automatic logic signed [MSG_WIDTH-1:0] apply_offset(
        input logic signed [MSG_WIDTH-1:0] value,
        input logic [MSG_WIDTH-1:0] beta  // Offset value
    );
        logic signed [MSG_WIDTH-1:0] abs_val, result;
        logic sign;
        
        sign = value[MSG_WIDTH-1];
        abs_val = sign ? -value : value;
        
        if (abs_val > beta) begin
            abs_val = abs_val - beta;
        end else begin
            abs_val = 0;
        end
        
        result = sign ? -abs_val : abs_val;
        return result;
    endfunction

endpackage : ldpc_decoder_pkg
