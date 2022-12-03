// Your code
`define AUIPC 4'd0
`define JAL   4'd1
`define JALR  4'd2
`define BEQ   4'd3
`define LW    4'd4
`define SW    4'd5
`define ADDI  4'd6
`define SLTI  4'd7
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
    // instruction reader's ports
    wire pause, state;
    wire [31:0] imm;
    // reg_file's input
    wire load;
    wire reg_wen;
    reg write_reg_number; // Current number of write register
    // Basic_ALU's inputs
    wire [31:0] in_A, in_B;
    wire pause;
    // Wires and regs for PC_next
    wire beq;
    reg [31:0] address;

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
        .imm(imm));

    Basic_ALU ALU0(
        .clk(clk),
        .rst_n(rst_n),
        .state(state),
        .in_A(in_A),
        .in_B(in_B),
        .pause(pause),
        .mem_addr_D(mem_addr_D));
    //==== Combinational Part =====================
    // Todo: any combinational/sequential circuit
    // inputs of reg0 (reg_file)
    assign rs1[5:0] = mem_rdata_I[19:15];
    assign rs2[5:0] = mem_rdata_I[24:20];
    assign rd[5:0]  = write_reg_number;
    assign rd_data[31:0] = clk ? mem_rdata_D : 
                    (state == JAL || state == JALR || state == AUIPC) ? address : mem_rdata_D;
    assign regWrite = clk ? load : reg_wen;
    //output of reg0
    assign mem_data_D[31:0] = rs2_data;
    // outputs of reader (instruction_analysis)
    assign mem_wen_D = (state == `SW) ? 1 : 0;
    assign load = (state == `LW) ? 1 : 0;
    assign reg_wen = (state != BEQ && state != LW)? 1 : 0;
    // inputs of ALU0 (Basic_ALU)
    assign in_A = (state == AUIPC || state == JAL || state == JALR) ? PC : rs1_data;
    assign in_B[31:0] = (state == ADD || state == SUB || state == XOR || state == MUL) ? rs2_data : imm;
    // PC_next's part
    assign beq = (rs1_data == rs2_data) ? 1 : 0;
    assign mem_addr_I = address;
    //==== Sequential Part ========================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00400000; // Do not modify this value!!!
        end
        else begin
            PC <= PC_nxt;
        end
    end
    // Todo: PC_next
    always @(*) begin
        if (pause) PC_next <= PC;
        else PC_next <= address;
    end

    always @(*) begin
        case(state)
            BEQ : begin
                if (beq) address <= PC + (imm << 1);
                else address <= PC+4;
            end
            JAL : address <= PC + imm;
            JALR : address <= imm;
            default : address <= PC + 4;
        endcase
    end

    always @(negedge clk or negedge rst_n) begin
        if (!rst_n) write_reg_number <= 5'd0;
        else write_reg_number <= mem_rdata_I[11:7];
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
            00100 : state_reg = (inst_code[13]) ? `SLTI : `ADDI;
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

    // Construct valid signal by positive edge of (state == MUL)
    wire valid, mul;
    reg mul_prev; 
    // Constant signal for multiplication mode
    wire [1:0] mul_mode;
    // result of ALU or of mulDiv
    reg [31:0] result, multiple_result; 

    wire ready;

    assign mem_addr_D = (state == MUL) ? multiple_result : result;
    assign mul = (state == MUL) ? 1 : 0;
    assign valid = (mul && !mul_prev) ? 1 : 0;
    assign mul_mode = 2'd0;
    assign pause = (valid || ready) ? 1 : 0;

    always  @(*) begin
        case(state)
            `JAL: result <= in_A + 4;
            `JALR: result <= in_A + 4;
            `SLTI: begin
                if (in_A < in_B) result <= 32'd1;
                else result <= 32'd0;
            `SUB: result <= in_A - in_B;
            `XOR: result <= in_A ^ in_B;
            default: result <= in_A + in_B;
        endcase
    end
    
    always @(posedge clk) begin
        mul_prev <= mul;
    end

    mulDiv hw2ALU(.clk(clk), .rst_n(rst_n), .valid(valid), .mode(mul_mode), .in_A(in_A), .in_B(in_B), .ready(ready), .out(multiple_result));

endmodule

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2
    // Definition of ports
    input         clk, rst_n;
    input         valid;
    input  [1:0]  mode; // mode: 0: mulu, 1: divu, 2: shift, 3: avg
    output        ready;
    input  [31:0] in_A, in_B;
    output [63:0] out;

    // Definition of states
    parameter IDLE = 3'd0;
    parameter MUL  = 3'd1;
    parameter DIV  = 3'd2;
    parameter SHIFT = 3'd3;
    parameter AVG = 3'd4;
    parameter OUT  = 3'd5;

    // Todo: Wire and reg if needed
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo: Instatiate any primitives if needed

    // Todo 5: Wire assignments
    assign ready = (state==OUT) ? 1 : 0;
    assign out = shreg;
    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) begin
                    case(mode)
                        2'd0 : state_nxt = MUL;
                        2'd1 : state_nxt = DIV;
                        2'd2 : state_nxt = SHIFT;
                        default : state_nxt = AVG;
                    endcase
                end
                else state_nxt = IDLE;
            end
            MUL: state_nxt = (counter == 5'd31) ? OUT : MUL;
            DIV: state_nxt = (counter == 5'd31) ? OUT : DIV;
            SHIFT : state_nxt = OUT;
            AVG : state_nxt = OUT;
            OUT : state_nxt = IDLE;
            default : state_nxt = IDLE;
        endcase
    end
    // Todo 2: Counter
    always @(*)begin
        if(state != MUL && state != DIV) begin
            counter_nxt = counter;
        end
        else counter_nxt = counter + 1;
    end
    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*) begin
        case(state)
        MUL : alu_out = alu_in + shreg[63:32];
        DIV : alu_out = shreg[63:31] - alu_in;
        default: alu_out = 33'd0;
        endcase
    end
    // Todo 4: Shift register
    always @(*) begin
        case(state)
        IDLE : begin
            if(valid) begin
                shreg_nxt[31:0] = in_A;
                shreg_nxt[63:32] = 32'd0;
            end
            else shreg_nxt = 64'd0;
        end
        MUL : begin
            shreg_nxt = shreg >> 1;
            if(shreg[0]) begin
                shreg_nxt[63:31] = alu_out;
            end
            else shreg_nxt = shreg_nxt;
        end
        DIV : begin
            shreg_nxt = shreg;
            if(shreg[63:31] > alu_in) begin
                shreg_nxt[63:31] = alu_out;
                shreg_nxt = shreg_nxt << 1;
                shreg_nxt[0] = 1;
            end
            else shreg_nxt = shreg_nxt << 1;
        end
        SHIFT : shreg_nxt = shreg >> alu_in[2:0];
        AVG : begin
            shreg_nxt[32:0] = shreg[31:0] + alu_in;
            shreg_nxt = shreg_nxt >> 1;
        end
        default: shreg_nxt = shreg;
        endcase
    end
    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            counter <= 5'd0;
            alu_in <= 32'd0;
            shreg <= 64'd0;
        end
        else begin
            state <= state_nxt;
            counter <= counter_nxt;
            alu_in <= alu_in_nxt;
            shreg <= shreg_nxt;
        end
    end

endmodule