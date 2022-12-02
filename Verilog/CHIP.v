// Your code
`define AUIPC 4'd0
`define JAL   4'd1
`define JALR  4'd2
`define BEQ   4'd3
`define LW    4'd4
`define SW    4'd5
`define ADDI  4'd6
`define STLI  4'd7
`define ADD   4'd8
`define SUB   4'd9
`define MUL   4'd10
`define XOR   4'd11
`define INV   4'd15

module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I
    );
    //==== I/O Declaration ========================
    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output [31:0] mem_addr_D ;
    output [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;

    //==== Reg/Wire Declaration ===================
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    wire   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg
    wire load;
    wire reg_wen;
    //==== Submodule Connection ===================
    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//

    // Todo: other submodules
    instruction_analysis reader(
        .clk(clk),
        .rst_n(rst_n),
        .pause(pause),
        .inst_code(mem_rdata_I),
        .state(state),
        .imm(imm)
        );
    //==== Combinational Part =====================
    assign mem_wen_D = (state == `SW) ? 1 : 0;
    assign load = (state == `LW) ? 1 : 0;
    assign reg_wen = (state != BEQ && state != LW)? 1 : 0;
    // Todo: any combinational/sequential circuit
    assign rs1[5:0] = mem_rdata_I[19:15];
    assign rs2[5:0] = mem_rdata_I[24:20];
    // assign rd[5:0]  = mem_rdata_I[11:7];
    //==== Sequential Part ========================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00400000; // Do not modify this value!!!
            
        end
        else begin
            PC <= PC_nxt;
            
        end
    end

endmodule

module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0; // zero: hard-wired zero
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'h7fffeffc; // sp: stack pointer
                    32'd3: mem[i] <= 32'h10008000; // gp: global pointer
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end
    end
endmodule

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2

endmodule

module Instruction_analysis(clk, rst_n, inst_code, pause, state, imm);
    
    input clk, rst_n, pause;
    input [31:0] inst_code; // instruction's binary code
    output [3:0] state;
    output [31:0] imm;

    reg [3:0] state_reg;
    reg stall, stall_next;
    reg [31:0] immediate;
    
    assign state = (!stall) ? state_reg : MUL;
    assign imm = immediate;

    always @(posedge clk) begin
        case(inst_code[6:2])
            00101 : state_reg = `AUIPC;
            11011 : state_reg = `JAL;
            11001 : state_reg = `JALR;
            11000 : state_reg = `BEQ;
            00000 : state_reg = `LW;
            01000 : state_reg = `SW;
            00100 : state_reg = (inst_code[13]) ? `STLI : `ADDI;
            01100 :
                if (inst_code[14]) inst = `XOR;
                else begin
                    case({inst_code[30],inst_code[15]})
                        00 : state_reg = `ADD;
                        10 : state_reg = `SUB;
                        01 : state_reg = `MUL;
                        default : state_reg = `INV;
                    endcase
                end
            default : state_reg = `INV;
        endcase
    end

    always @(posedge clk) begin
        if(!rst_n) stall <= 0;
        else stall <= stall_next;
    end
    always @(*) begin
        if(!rst_n) stall_next = 0;
        else begin
            if(pause) stall_next = !stall;
            else state_next = stall; 
        end
    end

    always @(*) begin
        case(state)
            `AUIPC : immediate = {inst_code[31:12], 12'd0};
            `JAL   : immediate = {11'd0, inst_code[31], inst_code[19:12], inst_code[20], inst_code[30:21], 1'd0};
            `BEQ   : immediate = {19'd0, inst_code[31], inst_code[7], inst_code[30:25], inst_code[11:8]};
            `SW    : immediate = {20'd0, inst_code[31:25], inst_code[11:7]};
            default : immediate = {20'd0, inst_code[31:20]};
        endcase
    end
endmodule

module Basic_ALU(clk, rst_n, state, in_A, in_B, pause, mem_addr_D);
    input clk, rst_n;
    input [3:0] state;
    input [31:0] in_A, in_B;
    output pause;
    output [31:0] mem_addr_D;

    reg valid, valid_next;
    reg [31:0] result, multiple_result;

    assign mem_addr_D = (state == MUL) ? multiple_result : result;

    always  @(*) begin
        case(state)
            `AUIPC:
            `JAL:
            `JALR:
            `BEQ:
            `LW:
            `SW:
            `ADDI:
            `STLI:
            `ADD:
            `SUB:
            `MUL:
            `XOR:
            default: result <= 32'd0;
        endcase

    end
    
endmodule