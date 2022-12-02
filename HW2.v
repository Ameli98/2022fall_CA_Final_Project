module ALU(
    clk,
    rst_n,
    valid,
    ready,
    mode,
    in_A,
    in_B,
    out
);

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