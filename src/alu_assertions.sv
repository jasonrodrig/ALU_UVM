

typedef enum{ADD,SUB,ADD_CIN,SUB_CIN,INC_A,DEC_A,INC_B,DEC_B,CMP,ADD_MUL,SH_MUL}arith;
typedef enum{AND,NAND,OR,NOR,XOR,XNOR,NOT_A,NOT_B,SHR1_A,SHL1_A,SHR1_B,SHL1_B,ROL_A_B,ROR_A_B}logical;
interface alu_assertions(clk,rst,ce,opa,opb,mode,inp_valid,cmd,cin,res,err,cout,oflow,g,l,e);
	input clk;
	input rst;
	input ce;
	input [`DATA_WIDTH - 1 : 0] opa;
	input [`DATA_WIDTH - 1 : 0]opb;
	input mode;
	input [1:0] inp_valid;
	input [`CMD_WIDTH - 1 : 0]cmd;
	input cin;
	input [RESULT_WIDTH - 1 : 0]res;
	input err,cout,oflow,g,l,e;

	property ALU_Known;
		@(posedge clk)
		##1 !($isunknown({rst,ce,opa,opb,mode,inp_valid,cmd,cin}));
	endproperty

	ALU_KNOWN: assert property(ALU_Known)
	$info("INPUTS SIGNALS ARE KNOWN: %d %d %d %d %d %d %d %d",rst,ce,opa,opb,mode,inp_valid,cmd,cin);
	else $info("INPUTS SIGNALS ARE UNKNOWN");

	ALU_RESET: assert property(@(posedge clk) ##10 !rst )
	$info("RESET IS NOT TRIGGERED");
	else $info("RESET IS TRIGGERED");

	property ALU_Clock_Enable;
		@(posedge clk)
		 //!ce |-> ##1res == ($past(res));
		 !ce |=> ($stable(res));
	endproperty

	ALU_CLOCK_ENABLE: assert property(ALU_Clock_Enable)
  $info("OUTPUTS ARE  LATCHED :%d %d %d %d %d %d %d",res,oflow,cout,g,l,e,err);
	else $info("OUTPUTS ARE NOT  LATCHED :%b %d %d %d %d %d %d",res,oflow,cout,g,l,e,err );

	/*
	property cycle16_interruption;
		@(posedge clk)
			( inp_valid == 1 || inp_valid == 2 ) |=> ##[1:15] res ;
	endproperty

	ALU_CLOCK_ENABLE: assert property(cycle16_interruption)
  $info("16_clock_cycle is interrupted");
	else $info("16_clock_cycle is not interrupted");
*/



endinterface
