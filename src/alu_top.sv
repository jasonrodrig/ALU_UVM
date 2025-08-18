`include "defines.sv"
`include "alu_design.sv"
`include "alu_interface.sv"
`include "alu_package.sv"
`include "alu_assertions.sv"
import uvm_pkg::*;
import alu_pkg::*;
module top;
	bit clk = 0;
//	bit rst;

	always #5 clk = ~clk;

/*	initial begin
		rst = 1;
		repeat(3)@(posedge clk);
		rst = 0;
	  end
*/
	
	alu_interface vif(clk);

	alu_design DUT(
		.CLK(vif.clk),
		.RST(vif.rst),
		.CE(vif.ce),
		.MODE(vif.mode),
		.CIN(vif.cin),
		.INP_VALID(vif.inp_valid),
		.CMD(vif.cmd),
		.OPA(vif.opa),
		.OPB(vif.opb),
		.RES(vif.res),
		.ERR(vif.err),
		.OFLOW(vif.oflow),
		.COUT(vif.cout),
		.G(vif.g),
		.L(vif.l),
		.E(vif.e)
	);

 bind vif alu_assertions ASSERT(
     .clk(vif.clk),
	   .rst(vif.rst),
	   .ce(vif.ce),
	   .mode(vif.mode),
	   .cin(vif.cin),
	   .inp_valid(vif.inp_valid),
	   .cmd(vif.cmd),
	   .opa(vif.opa),
	   .opb(vif.opb),
	   .res(vif.res),
	   .err(vif.err),
	   .oflow(vif.oflow),
	   .cout(vif.cout),
	   .g(vif.g),
	   .l(vif.l),
	   .e(vif.e)
 );

	initial begin 
		uvm_config_db#(virtual alu_interface)::set(null,"*","vif",vif);
		$dumpfile("dump.vcd");
		$dumpvars;
	end

	initial begin 
		run_test("alu_regression_test");
		#1000 $finish;
	end
endmodule
