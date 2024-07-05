
`timescale 1ns/100ps

   `define ADD  4'b0000
   `define SUB  4'b0001
   `define SLT  4'b0010
   `define SLTU 4'b0011
   `define AND  4'b0100
   `define XOR  4'b0101
   `define OR   4'b0110
   `define NOR  4'b0111
   `define LUI  4'b1000

module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;
   reg [31:0] A, B, PC, IR, MDR, MAR;

   // Data Path Control Lines, don't forget, regs are not always register !!
   reg setMRE, clrMRE, setMWE, clrMWE;
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, MDRwrt, MARwrt;

   // Memory Ports Bindings
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Line
   reg [3:0] aluOp;
   reg [2:0] aluSelB;
   reg SgnExt, aluSelA, IorD;
   reg [2:0] MemtoReg;
	reg [1:0] RegDst;	
   
   // We need PC Src when we implement jump and etc.
	reg [1:0] PC_Src;	

   // Regs And Wires For Mult
	reg start;
	wire ready;
	wire [63:0] Product;	

   // Reg For MFLO & MFHI
	reg H, L;

   // Wiring & AluResult reg
   wire aluZero;
   wire [31:0] aluResult, rfRD1, rfRD2;
   reg [31:0] AluResult;

   // Clocked Registers
   always @( posedge clk ) begin
      case (PC_Src)
         2'b00: AluResult = aluResult;
         2'b01: AluResult = {PC[31:28] , IR[25:0] , 2'b00}; 
         2'b10: AluResult = A;
      endcase

      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt )
         PC <= #0.1 AluResult;

      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? AluResult : PC;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;
   end

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};

   // WR with JAL & JALR
   wire [4:0] WR_w =  RegDst == 1 ? IR[15:11] : RegDst == 2 ? 5'b11111 : IR[20:16];

   // WD with attention to Low or Hi in mult product
   wire [31:0] WD_w = H ? Product[63:32] : L ? Product[31:0] :  MemtoReg ==1 ? MDR : MemtoReg == 2 ? SZout : aluResult;

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

		.WR		( WR_w ), 
		.WD		( WD_w ) 
   );


   // ALU-A Mux
   wire [31:0] aluA = aluSelA ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (aluSelB)
		3'b000: aluB = B;
		3'b001: aluB = 32'h4;
		3'b010: aluB = SZout;
		3'b011: aluB = SZout << 2;
		3'b100: aluB = 32'b0;
   endcase

   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),

      .X( aluResult ),
      .Z( aluZero )
   );

	multiplier2 mult_u
	(
		.clk		( clk ),
		.start	( start ),
		.A			( A ),
		.B			( B ),
		
		.Product	( Product ),
		.ready	( ready )
	);

   // Controller Starts Here

   // Controller State Registers
   reg [5:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_ALU_R = 7, EX_ALU_I = 8,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_BRA_1 = 25, EX_BRA_2 = 26, EX_J = 27, EX_JAL = 28, EX_JR = 29, EX_JALR = 30,
   	EX_MULTU_1 = 31, EX_MULTU_2 =32, EX_MULTU_3 = 33, EX_MFLO = 34, EX_MFHI = 35;

   // State Clocked Register 
	always @( posedge clk )
		if( reset )
			state <= #0.1 RESET;
		else
			state <= #0.1 nxt_state;
	
	task PrepareFetch;
		begin
			IorD = 0;
			setMRE = 1;
			MARwrt = 1;
			nxt_state = FETCH1;
		end
	endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      SgnExt = 'bx; IorD = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;
      aluSelA = 'bx; aluSelB = 'bx; aluOp = 'bx;

      PCwrt = 0;
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;
      PC_Src = 0; // Jump and etc
      start = 0; // For mult
      H = 0; L = 0; // MFLO & MFHI

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 3'b001;
            aluOp = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000: begin             // R-format
                  case( IR[5:3] )
                     3'b000: ;
                     3'b001: ;
                     3'b010: ;
                     3'b011: ;
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;
                     3'b110: ;
                     3'b111: ;
                  endcase

						case( IR[5:0] )
                     6'b011001: nxt_state = EX_MULTU_1;//mult
							6'b001000: nxt_state = EX_JR;//jr
							6'b001001: nxt_state = EX_JALR;//jalr  
							6'b010000: nxt_state = EX_MFHI;//mfhi
							6'b010010: nxt_state = EX_MFLO;//mflo
                  endcase
               end
							
               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110,             // xori
					6'b001_111:             // lui
                  nxt_state = EX_ALU_I;

               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b000_100,
               6'b000_101:
                  nxt_state = EX_BRA_1;

					6'b000_010: 
                  nxt_state = EX_J;   
					
					6'b000_011: 
                  nxt_state = EX_JAL;
               
               

               // rest of instructiones should be decoded here

            endcase
         end

         EX_ALU_R: begin
            aluSelA = 1;
				aluSelB = 2'b00;
				RegDst = 2'b01;
				MemtoReg = 3'b000;
				RFwrt = 1;

				case( IR[5:0] )
					6'b100000: aluOp = `ADD;//add
					6'b100001: aluOp = `ADD;//add(u)
					6'b100010: aluOp = `SUB;//sub
					6'b100011: aluOp = `SUB;//sub(u)
					6'b100100: aluOp = `AND;//and
					6'b100101: aluOp = `OR;//or
					6'b100110: aluOp = `XOR;//xor
					6'b100111: aluOp = `NOR;//nor
					6'b101010: aluOp = `SLT;//slt
					6'b101011: aluOp = `SLTU;//slt(u)
				endcase

            PrepareFetch; 
         end

         EX_ALU_I: begin
            aluSelA = 1;
				aluSelB = 3'b010;
				RegDst = 2'b00;
				MemtoReg = 3'b000;
				RFwrt = 1;
            SgnExt = 0;

				case( IR[28:26] )
					3'b000: begin //addi
                  aluOp = `ADD; 
                  SgnExt = 1; 
               end
					3'b010: begin //slti
                  aluOp = `SLT;
                  SgnExt = 1; 
               end 
					3'b001: aluOp = `ADD;//add(u)
					3'b100: aluOp = `AND;//andi 
					3'b101: aluOp = `OR;//ori
					3'b110: aluOp = `XOR;//xori
					3'b011: aluOp = `SLTU;//slti(u)
					3'b111: aluOp = `LUI;//lui

				endcase
				
				PrepareFetch;
         end

         EX_LW_1: begin
				aluSelA = 1;
				aluSelB = 3'b010;
				IorD = 1;
				MARwrt = 1;
				setMRE = 1;
				SgnExt = 1;
            aluOp = `ADD;

				nxt_state = EX_LW_2;
         end

			EX_LW_2: 
            nxt_state = EX_LW_3;

			EX_LW_3: 
            nxt_state = EX_LW_4;
			
			EX_LW_4: begin
				MDRwrt = 1;
				clrMRE = 1;

				nxt_state = EX_LW_5;
			end

			EX_LW_5: begin
				RFwrt = 1;
				RegDst = 2'b00;
				MemtoReg = 3'b001;

				PrepareFetch;
			end

         EX_SW_1: begin
				aluSelA = 1;
				aluSelB = 3'b010;
				IorD = 1;
				MARwrt = 1;
				setMWE = 1;
            aluOp = `ADD;

				nxt_state = EX_SW_2;
         end

			EX_SW_2: begin 
            clrMWE = 1; 
   
            nxt_state = EX_SW_3; 
         end

			EX_SW_3: PrepareFetch;

         EX_BRA_1: begin
            aluSelA = 1;
            aluSelB = 3'b000;
            aluOp = `SUB;

            case(IR[31:26])
               6'b000100:begin
                  nxt_state = (aluZero ? EX_BRA_2 : RESET);
               end
               
               6'b000101:begin
                  nxt_state = (!aluZero ? EX_BRA_2 : RESET);
               end

            endcase

         end

         EX_BRA_2: begin
            aluSelA = 0;
            aluSelB = 3'b011;
            IorD = 1;
            MARwrt = 1;
            setMRE = 1;
            PCwrt = 1;
            aluOp = `ADD;
            SgnExt = 1;

            nxt_state = FETCH1;
         end

			EX_J: begin
				IorD = 1;
				MARwrt = 1;
				setMRE = 1;
				PCwrt = 1;
				PC_Src = 2'b01;

				nxt_state = FETCH1;
			end

			EX_JAL: begin
				aluSelA = 0;
				aluSelB = 3'b100;
				IorD = 1;
				RegDst = 2'b10;
				RFwrt = 1;
				MemtoReg = 0;
				setMRE = 1;
				PCwrt = 1;
				aluOp = `ADD;
				MARwrt = 1;
				PC_Src = 2'b01;

				nxt_state = FETCH1;
			end
         
			EX_JR: begin
				IorD = 1;
				setMRE = 1;
				PCwrt = 1;
				MARwrt = 1;
				PC_Src = 2'b10;

				nxt_state = FETCH1;
			end

			EX_JALR: begin
				aluSelA = 0;
				aluSelB = 3'b100;
				IorD = 1;
				RegDst = 2'b10;
				RFwrt = 1;
				MemtoReg = 0;
				setMRE = 1;
				PCwrt = 1;
				aluOp = `ADD;
				MARwrt = 1;
				PC_Src = 2'b10;
				
				nxt_state = FETCH1;
			end

         EX_MULTU_1: begin 
            start = 1;

            nxt_state = EX_MULTU_2;
         end

         EX_MULTU_2: begin 
            if ( ready == 1 )
               nxt_state = EX_MULTU_3;
            else
               nxt_state = EX_MULTU_2;
         end

         EX_MULTU_3: begin 

            PrepareFetch;
         end

			EX_MFHI: begin
				H = 1;
				RegDst = 2'b01;
				RFwrt = 1;

				PrepareFetch;
			end
			
			EX_MFLO: begin
				L = 1;
				RegDst = 2'b01;
				RFwrt = 1;

				PrepareFetch;
			end

      endcase

   end

endmodule


//==============================================================================

module my_alu(
   input [3:0] Op,
   input [31:0] A,
   input [31:0] B,

   output [31:0] X,
   output        Z
);

   wire sub = Op != `ADD;

   wire [31:0] bb = sub ? ~B : B;

   wire [32:0] sum = A + bb + sub;

   wire sltu = ! sum[32];

   wire v = sub ? 
        ( A[31] != B[31] && A[31] != sum[31] )
      : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         `LUI : x = {B[15:0], 16'b0};
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

//==============================================================================

module multiplier2(
//---------------------Port directions and deceleration
   input clk,  
   input start,
   input [31:0] A,
   input [31:0] B, 
   output reg [63:0] Product,
   output ready
    );



//----------------------------------------------------

//--------------------------------- register deceleration
reg [31:0] Multiplicand;
reg [5:0] counter;
//-----------------------------------------------------

//----------------------------------- wire deceleration
wire [31:0] adder_output;
wire c_out;
//-------------------------------------------------------

//------------------------------------ combinational logic
assign ready = counter[5];
assign {c_out, adder_output} = Product[63:32] + (Product[0] ? Multiplicand : 32'b0);
//-------------------------------------------------------

//------------------------------------- sequential Logic
always @ (posedge clk)

   if(start) begin
      counter <= 6'h0 ;
      Multiplicand <= A;
      Product <= {32'b0, B};
   end

   else if(! ready) begin
         Product <= {c_out, adder_output, Product[31:1]};
         counter <= counter + 1;
   end   

endmodule