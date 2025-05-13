`timescale 1ns / 1ps

// TOP
// -------------------------------------
module top
#(parameter
    WORD_SIZE = 8,
    SEL1_SIZE = 3,
    SEL2_SIZE = 2
)(
    input   clk, rst
);
    wire [WORD_SIZE-1:0] instruction, address, bus_1, mem_word;
    wire [SEL1_SIZE-1:0] sel_bus_1_mux;
    wire [SEL2_SIZE-1:0] sel_bus_2_mux;
    wire                 load_r0,
                         load_r1,
                         load_r2,
                         load_r3,
                         load_pc,
                         load_ir,
                         load_add_r,
                         load_reg_y,
                         load_reg_z,
                         inc_pc,
                         write,
                         zero;

    Processing_Unit Processor (
        // Outputs
        .instruction   ( instruction   ),
        .address       ( address       ),
        .bus_1         ( bus_1         ),
        .zero          ( zero          ),
        // Inputs
        .clk           ( clk           ),
        .rst           ( rst           ),
        .load_r0       ( load_r0       ),
        .load_r1       ( load_r1       ),
        .load_r2       ( load_r2       ),
        .load_r3       ( load_r3       ),
        .load_pc       ( load_pc       ),
        .load_ir       ( load_ir       ),
        .load_add_r    ( load_add_r    ),
        .load_reg_y    ( load_reg_y    ),
        .load_reg_z    ( load_reg_z    ),
        .inc_pc        ( inc_pc        ),
        .sel_bus_1_mux ( sel_bus_1_mux ),
        .sel_bus_2_mux ( sel_bus_2_mux ),
        .mem_word      ( mem_word      )
    );

    Control_Unit    Controller (
        // Outputs
        .sel_bus_1_mux ( sel_bus_1_mux ),
        .sel_bus_2_mux ( sel_bus_2_mux ),
        .load_r0       ( load_r0       ),
        .load_r1       ( load_r1       ),
        .load_r2       ( load_r2       ),
        .load_r3       ( load_r3       ),
        .load_pc       ( load_pc       ),
        .load_ir       ( load_ir       ),
        .load_add_r    ( load_add_r    ),
        .load_reg_y    ( load_reg_y    ),
        .load_reg_z    ( load_reg_z    ),
        .inc_pc        ( inc_pc        ),
        .write         ( write         ),
        // Inputs
        .clk           ( clk           ),
        .rst           ( rst           ),
        .zero          ( zero          ),
        .instruction   ( instruction   )
    );

    Memory_Unit     Memory (
        // Outputs
        .data_out ( mem_word ),
        // Inputs
        .data_in  ( bus_1    ),
        .clk      ( clk      ),
        .address  ( address  ),
        .write    ( write    )
    );

endmodule


// PROCESSING UNIT
// -------------------------------------
module Processing_Unit
#(parameter
    WORD_SIZE = 8,
    OP_SIZE   = 4,
    SEL1_SIZE = 3,
    SEL2_SIZE = 2
)(
    output [WORD_SIZE-1:0] instruction, address, bus_1,
    output                 zero,
    input  [WORD_SIZE-1:0] mem_word,
    input  [SEL1_SIZE-1:0] sel_bus_1_mux,
    input  [SEL2_SIZE-1:0] sel_bus_2_mux,
    input                  load_r0, load_r1, load_r2, load_r3, load_pc, inc_pc,
    input                  load_ir, load_add_r, load_reg_y, load_reg_z, clk, rst
);
    wire  [OP_SIZE-1:0]   opcode = instruction [WORD_SIZE-1:WORD_SIZE-OP_SIZE];
    wire  [WORD_SIZE-1:0] bus_2;
    wire  [WORD_SIZE-1:0] r0_out, r1_out, r2_out, r3_out;
    wire  [WORD_SIZE-1:0] pc_count, y_value, alu_out;
    wire                  alu_zero_flag;

    Register_Unit R0
    (
        .data_out ( r0_out  ),
        .data_in  ( bus_2   ),
        .load     ( load_r0 ),
        .clk      ( clk     ),
        .rst      ( rst     )
    );
    Register_Unit R1
    (
        .data_out ( r1_out  ),
        .data_in  ( bus_2   ),
        .load     ( load_r1 ),
        .clk      ( clk     ),
        .rst      ( rst     )
    );
    Register_Unit R2
    (
        .data_out ( r2_out  ),
        .data_in  ( bus_2   ),
        .load     ( load_r2 ),
        .clk      ( clk     ), 
        .rst      ( rst     )
    );
    Register_Unit R3
    (
        .data_out ( r3_out  ),
        .data_in  ( bus_2   ),
        .load     ( load_r3 ),
        .clk      ( clk     ),
        .rst      ( rst     )
    );
    Register_Unit Reg_Y
    (
        .data_out ( y_value    ),
        .data_in  ( bus_2      ),
        .load     ( load_reg_y ),
        .clk      ( clk        ),
        .rst      ( rst        )
    );
    D_flop Reg_Z
    (
        .data_out ( zero          ),
        .data_in  ( alu_zero_flag ),
        .load     ( load_reg_z    ),
        .clk      ( clk           ),
        .rst      ( rst           )
    );
    Address_Register Add_R 
    (
        .data_out ( address    ),
        .data_in  ( bus_2      ),
        .load     ( load_add_r ),
        .clk      ( clk        ),
        .rst      ( rst        )
    );
    Instruction_Register IR
    (
        .data_out ( instruction ),
        .data_in  ( bus_2       ),
        .load     ( load_ir     ),
        .clk      ( clk         ),
        .rst      ( rst         )
    );
    Program_Counter PC
    (
        .count    ( pc_count ),
        .data_in  ( bus_2    ),
        .load_pc  ( load_pc  ),
        .inc_pc   ( inc_pc   ),
        .clk      ( clk      ),
        .rst      ( rst      )
    );
    Multiplexer_5ch Mux_1
    (
        .mux_out ( bus_1         ),
        .data_a  ( r0_out        ),
        .data_b  ( r1_out        ),
        .data_c  ( r2_out        ),
        .data_d  ( r3_out        ),
        .data_e  ( pc_count      ),
        .sel     ( sel_bus_1_mux )
    );
    Multiplexer_3ch Mux_2
    (
        .mux_out ( bus_2         ),
        .data_a  ( alu_out       ),
        .data_b  ( bus_1         ),
        .data_c  ( mem_word      ),
        .sel     ( sel_bus_2_mux )
    );
    AL_Unit ALU
    (
        .alu_out       ( alu_out       ),
        .alu_zero_flag ( alu_zero_flag ),
        .data_1        ( y_value       ),
        .data_2        ( bus_1         ),
        .opcode        ( opcode        )
    );

endmodule


// REGISTER UNIT
// -------------------------------------
module Register_Unit
#(parameter
    WORD_SIZE = 8
)(
    output reg [WORD_SIZE-1:0] data_out,
    input      [WORD_SIZE-1:0] data_in,
    input                      load, clk, rst
);
    always @ (posedge clk, negedge rst)
        if (rst == 1'b0) data_out <= 0;
        else if (load) data_out <= data_in;

endmodule


// D FLOP
// -------------------------------------
module D_flop
(
    output  reg data_out,
    input       data_in, load, clk, rst
);
    always @ (posedge clk, negedge rst)
        if (rst == 1'b0) data_out <= 0;
        else if (load == 1'b1) data_out <= data_in;

endmodule


// ADDRESS REGISTER
// -------------------------------------
module Address_Register
#(parameter
    WORD_SIZE = 8
)(
    output reg [WORD_SIZE-1:0] data_out,
    input      [WORD_SIZE-1:0] data_in,
    input                      load, clk, rst
);
    always @ (posedge clk, negedge rst)
        if (rst == 1'b0) data_out <= 0;
        else if (load == 1'b1) data_out <= data_in;

endmodule


// INSTRUCTION REGISTER
// -------------------------------------
module Instruction_Register
#(parameter
    WORD_SIZE = 8
)(
    output reg [WORD_SIZE-1:0] data_out,
    input      [WORD_SIZE-1:0] data_in,
    input                      load, clk, rst
);
    always @ (posedge clk, negedge rst)
        if (rst == 1'b0) data_out <= 0;
        else if (load == 1'b1) data_out <= data_in;

endmodule


// PROGRAM COUNTER
// -------------------------------------
module Program_Counter
#(parameter
    WORD_SIZE = 8
)(
    output reg [WORD_SIZE-1:0] count,
    input      [WORD_SIZE-1:0] data_in,
    input                      load_pc, inc_pc,
    input                      clk, rst
);
    always @ (posedge clk, negedge rst)
        if (rst == 1'b0) count <= 0;
        else if (load_pc == 1'b1) count <= data_in;
        else if (inc_pc == 1'b1) count <= count + 1;

endmodule


// MULTIPLEXER 5CH
// -------------------------------------
module Multiplexer_5ch
#(parameter
    WORD_SIZE = 8
)(
    output [WORD_SIZE-1:0] mux_out,
    input  [WORD_SIZE-1:0] data_a, data_b, data_c, data_d, data_e,
    input  [2:0]           sel
);
    assign mux_out = (sel == 0) ? data_a:
                     (sel == 1) ? data_b:
                     (sel == 2) ? data_c:
                     (sel == 3) ? data_d:
                     (sel == 4) ? data_e: 8'b0;

endmodule


// MULTIPLEXER 3CH
// -------------------------------------
module Multiplexer_3ch
#(parameter
    WORD_SIZE = 8
)(
    output  [WORD_SIZE-1:0] mux_out,
    input   [WORD_SIZE-1:0] data_a, data_b, data_c,
    input   [1:0]           sel
);
    assign mux_out = (sel == 0) ? data_a:
                     (sel == 1) ? data_b:
                     (sel == 2) ? data_c: 8'b0;
endmodule


// AL UNIT
// -------------------------------------
module AL_Unit
#(parameter
    WORD_SIZE = 8,
    OP_SIZE   = 4,
    NOP       = 4'b0000,
    ADD       = 4'b0001,
    SUB       = 4'b0010,
    AND       = 4'b0011,
    NOT       = 4'b0100,
    RD        = 4'b0101,
    WR        = 4'b0110,
    BR        = 4'b0111,
    BRZ       = 4'b1000
)(
    output reg [WORD_SIZE-1:0] alu_out,
    output                     alu_zero_flag,
    input      [WORD_SIZE-1:0] data_1, data_2,
    input      [OP_SIZE-1:0]   opcode
);
    assign alu_zero_flag = ~|alu_out;

    always @ (opcode, data_1, data_2)
        case(opcode)
            NOP: alu_out = 0;
            ADD: alu_out = data_1 + data_2;
            SUB: alu_out = data_1 - data_2;
            AND: alu_out = data_1 & data_2;
            NOT: alu_out = ~data_2;
            default: alu_out = 0;
        endcase

endmodule


// CONTROL UNIT
// -------------------------------------
module Control_Unit
#(parameter
    WORD_SIZE  = 8,
    OP_SIZE    = 4,
    STATE_SIZE = 4,
    SRC_SIZE   = 2,
    DEST_SIZE  = 2,
    SEL1_SIZE  = 3,
    SEL2_SIZE  = 2,
    NOP        = 0,
    ADD        = 1,
    SUB        = 2,
    AND        = 3,
    NOT        = 4,
    RD         = 5,
    WR         = 6,
    BR         = 7,
    BRZ        = 8,
    R0         = 0,
    R1         = 1,
    R2         = 2,
    R3         = 3,
    S_IDLE     = 0,
    S_FET1     = 1,
    S_FET2     = 2,
    S_DEC      = 3,
    S_EX1      = 4,
    S_RD1      = 5,
    S_RD2      = 6,
    S_WR1      = 7,
    S_WR2      = 8,
    S_BR1      = 9,
    S_BR2      = 10,
    S_HALT     = 11
)(
    output     [SEL1_SIZE-1:0] sel_bus_1_mux,
    output     [SEL2_SIZE-1:0] sel_bus_2_mux,
    output reg                 load_r0, load_r1, load_r2, load_r3, load_pc, inc_pc,
                               load_ir, load_add_r, load_reg_y, load_reg_z, write,
    input      [WORD_SIZE-1:0] instruction,
    input                      zero, clk, rst
);
    reg  [STATE_SIZE-1:0] state, next_state;
    reg                   sel_alu, sel_bus_1, sel_mem;
    reg                   sel_r0, sel_r1, sel_r2, sel_r3, sel_pc;
    reg                   err_flag;
    wire [OP_SIZE-1:0]    opcode = instruction [WORD_SIZE-1:WORD_SIZE-OP_SIZE];
    wire [SRC_SIZE-1:0]   src    = instruction [SRC_SIZE+DEST_SIZE-1:DEST_SIZE];
    wire [DEST_SIZE-1:0]  dest   = instruction [DEST_SIZE-1:0];

    assign sel_bus_1_mux[SEL1_SIZE-1:0] = sel_r0 ? 0:
                                          sel_r1 ? 1:
                                          sel_r2 ? 2:
                                          sel_r3 ? 3:
                                          sel_pc ? 4: 3'b0;

    assign sel_bus_2_mux[SEL2_SIZE-1:0] = sel_alu   ? 0:
                                          sel_bus_1 ? 1:
                                          sel_mem   ? 2: 2'b0;

    always @ (posedge clk, negedge rst) begin
        if(rst == 0)
            state <= S_IDLE;
        else state <= next_state;
    end

    always @ (clk, src, dest, state, opcode, zero) begin
        sel_r0     = 0;
        sel_r1     = 0;
        sel_r2     = 0;
        sel_r3     = 0;
        sel_pc     = 0;
        load_r0    = 0;
        load_r1    = 0;
        load_r2    = 0;
        load_r3    = 0;
        load_pc    = 0;
        load_ir    = 0;
        load_add_r = 0;
        load_reg_y = 0;
        load_reg_z = 0;
        inc_pc     = 0;
        sel_bus_1  = 0;
        sel_alu    = 0;
        sel_mem    = 0;
        write      = 0;
        err_flag   = 0;
        next_state = state;

        case(state)
            S_IDLE: next_state = S_FET1;

            S_FET1: begin
                next_state = S_FET2;
                sel_pc     = 1;
                sel_bus_1  = 1;
                load_add_r = 1;
            end

            S_FET2: begin
                next_state = S_DEC;
                sel_mem    = 1;
                load_ir    = 1;
                inc_pc     = 1;
            end

            S_DEC:
                case(opcode)
                    NOP: next_state = S_FET1;
                    ADD, SUB, AND: begin
                        next_state = S_EX1;
                        sel_bus_1  = 1;
                        load_reg_y = 1;
                        case(src)
                            R0: sel_r0 = 1;
                            R1: sel_r1 = 1;
                            R2: sel_r2 = 1;
                            R3: sel_r3 = 1;
                            default: err_flag = 1;
                        endcase
                    end

                    NOT: begin
                        next_state = S_FET1;
                        load_reg_z = 1;
                        sel_alu    = 1;
                        case(src)
                            R0: sel_r0 = 1;
                            R1: sel_r1 = 1;
                            R2: sel_r2 = 1;
                            R3: sel_r3 = 1;
                            default: err_flag = 1;
                        endcase
                        case(dest)
                            R0: load_r0 = 1;
                            R1: load_r1 = 1;
                            R2: load_r2 = 1;
                            R3: load_r3 = 1;
                            default: err_flag = 1;
                        endcase
                    end

                    RD: begin
                        next_state = S_RD1;
                        sel_pc     = 1;
                        sel_bus_1  = 1;
                        load_add_r = 1;
                    end

                    WR: begin
                        next_state = S_WR1;
                        sel_pc     = 1;
                        sel_bus_1  = 1;
                        load_add_r = 1;
                    end

                    BR: begin
                        next_state = S_BR1;
                        sel_pc     = 1;
                        sel_bus_1  = 1;
                        load_add_r = 1;
                    end

                    BRZ:
                        if (zero == 1) begin
                            next_state = S_BR1;
                            sel_pc     = 1;
                            sel_bus_1  = 1;
                            load_add_r = 1;
                        end
                        else begin
                            next_state = S_FET1;
                            inc_pc     = 1;
                        end
                    default: next_state = S_HALT;
                endcase

            S_EX1: begin
                next_state = S_FET1;
                load_reg_z = 1;
                sel_alu    = 1;
                case(dest)
                    R0: begin sel_r0 = 1; load_r0 = 1; end
                    R1: begin sel_r1 = 1; load_r1 = 1; end
                    R2: begin sel_r2 = 1; load_r2 = 1; end
                    R3: begin sel_r3 = 1; load_r3 = 1; end
                    default: err_flag = 1;
                endcase
            end

            S_RD1: begin
                next_state = S_RD2;
                sel_mem    = 1;
                load_add_r = 1;
                inc_pc     = 1;
            end

            S_WR1: begin
                next_state = S_WR2;
                sel_mem    = 1;
                load_add_r = 1;
                inc_pc     = 1;
            end

            S_RD2: begin
                next_state = S_FET1;
                sel_mem    = 1;
                case(dest)
                    R0: load_r0 = 1;
                    R1: load_r1 = 1;
                    R2: load_r2 = 1;
                    R3: load_r3 = 1;
                    default: err_flag = 1;
                endcase
            end

            S_WR2: begin
                next_state = S_FET1;
                write      = 1;
                case(src)
                    R0: sel_r0 = 1;
                    R1: sel_r1 = 1;
                    R2: sel_r2 = 1;
                    R3: sel_r3 = 1;
                    default: err_flag = 1;
                endcase
            end

            S_BR1: begin
                next_state = S_BR2;
                sel_mem    = 1;
                load_add_r = 1;
            end

            S_BR2: begin
                next_state = S_FET1;
                sel_mem    = 1;
                load_pc    = 1;
            end

            S_HALT: next_state = S_HALT;

            default: next_state = S_IDLE;
        endcase
    end

endmodule


// MEMORY UNIT
// -------------------------------------
module Memory_Unit
#(parameter
    WORD_SIZE   = 8,
    MEMORY_SIZE = 256
)(
    output [WORD_SIZE-1:0] data_out,
    input  [WORD_SIZE-1:0] data_in,
    input  [WORD_SIZE-1:0] address,
    input                  clk, write
);

    reg [WORD_SIZE-1:0] memory  [MEMORY_SIZE-1:0];

    assign data_out = memory[address];

    always @ (posedge clk)
        if (write) memory[address] <= data_in;

endmodule

