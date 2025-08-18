

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

	property ALU_Unknown;
		@(posedge clk)
			!($isunknown({rst,ce,opa,opb,mode,inp_valid,cmd,cin}));
	endproperty

	ALU_UNKNOWN: assert property(ALU_Unknown)
	$info("INPUTS SIGNALS ARE KNOWN");
	else $info("INPUTS ARE UNKNOWN : %d %d %d %d %d %d %d %d", rst,ce,opa,opb,mode,inp_valid,cmd,cin);

	ALU_RESET: assert property(@(posedge clk) rst) 
	$info("RESET IS TRIGGERED");
	else $info("RESET IS NOT TRIGGERED");


	property ALU_Clock_Enable;
		@(posedge clk)
			ce |-> res == $past(res);
	endproperty

	ALU_CLOCK_ENABLE: assert property(ALU_Clock_Enable)
	$info("OUTPUTS ARE NOT LATCHED");
	else $info("OUTPUTS ARE LATCHED : %d %d %d %d %d %d %d",res,oflow,cout,g,l,e,err);

endinterface
