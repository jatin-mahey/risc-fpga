`timescale 1ns / 1ps

// RISC TESTBENCH ---------------------
// -------------------------------------
// 
//
// -------------------------------------
module tb_top
#(parameter
    WORD_SIZE = 8
)();
    reg  [8:0]  k;
    reg         rst;
    wire        clk;

    Clock_Unit  M1  (clk);
    top         M2  (clk, rst);

    wire [WORD_SIZE-1:0]    word0,   word1,   word2,   word3,   word4,   word5,
                            word6,   word7,   word8,   word9,   word10,  word11,
                            word12,  word13,  word14,  word128, word129, word130, 
                            word131, word132, word133, word134, word135, word136,
                            word137, word138, word139, word140, word255;

    assign  word0   = M2.Memory.memory[0],
            word1   = M2.Memory.memory[1],
            word2   = M2.Memory.memory[2],
            word3   = M2.Memory.memory[3],
            word4   = M2.Memory.memory[4],
            word5   = M2.Memory.memory[5],
            word6   = M2.Memory.memory[6],
            word7   = M2.Memory.memory[7],
            word8   = M2.Memory.memory[8],
            word9   = M2.Memory.memory[9],
            word10  = M2.Memory.memory[10],
            word11  = M2.Memory.memory[11],
            word12  = M2.Memory.memory[12],
            word13  = M2.Memory.memory[13],
            word14  = M2.Memory.memory[14],
            word128 = M2.Memory.memory[128],
            word129 = M2.Memory.memory[129],
            word130 = M2.Memory.memory[130],
            word131 = M2.Memory.memory[131],
            word132 = M2.Memory.memory[132],
            word133 = M2.Memory.memory[133],
            word134 = M2.Memory.memory[134],
            word135 = M2.Memory.memory[135],
            word136 = M2.Memory.memory[136],
            word137 = M2.Memory.memory[137],
            word138 = M2.Memory.memory[138],
            word139 = M2.Memory.memory[139],
            word140 = M2.Memory.memory[140],
            word255 = M2.Memory.memory[255];


    initial #2800 $finish;

    initial begin: Flush_Memory
        #2 rst = 0;
        for (k=0; k<=255; k=k+1)
            M2.Memory.memory[k] = 0;
            #10 rst = 1;
    end

    initial begin: Load_Program
        #5
        M2.Memory.memory[0]   = 8'b0000_00_00;                              // NOP XX XX
        M2.Memory.memory[1]   = 8'b0101_00_00; M2.Memory.memory[2]   = 128; // LDR XX R0 128
        M2.Memory.memory[3]   = 8'b0101_00_01; M2.Memory.memory[4]   = 129; // LDR XX R1 129
        M2.Memory.memory[5]   = 8'b0101_00_10; M2.Memory.memory[6]   = 130; // LDR XX R2 130
        M2.Memory.memory[7]   = 8'b0101_00_11; M2.Memory.memory[8]   = 131; // LDR XX R3 131
        M2.Memory.memory[9]   = 8'b0010_00_01;                              // SUB R1 R0
        M2.Memory.memory[10]  = 8'b1000_00_00; M2.Memory.memory[11]  = 134; // BRZ XX XX 134
        M2.Memory.memory[12]  = 8'b0110_00_00;                              // STR XX R3
        M2.Memory.memory[13]  = 8'b0111_00_11; M2.Memory.memory[14]  = 140; // BR  XX XX 140
        M2.Memory.memory[128] = 10;
        M2.Memory.memory[129] = 20;
        M2.Memory.memory[130] = 30;
        M2.Memory.memory[131] = 40;
        M2.Memory.memory[134] = 139;
        M2.Memory.memory[139] = 8'b0000_00_00;
        M2.Memory.memory[140] = 9;
    end
endmodule

// CLOCK UNIT --------------------------
// -------------------------------------
//
//
// -------------------------------------
module Clock_Unit
(
    output reg clock
);

    localparam delay = 0;
    localparam half_cycle = 10;

    initial begin
        #delay clock = 0;
        forever #half_cycle clock = ~clock;
    end

endmodule

