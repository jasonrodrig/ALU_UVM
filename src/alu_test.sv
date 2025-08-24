class alu_test extends uvm_test;

	// registering alu_test with the fatcory
	`uvm_component_utils(alu_test)

	// handle declaration for alu_environment and alu_test
	alu_environment alu_env;
	alu_sequence seq;

	//------------------------------------------------------//
	//    Creating a new constructor for alu_test           //  
	//------------------------------------------------------//

	function new(string name = "alu_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	//------------------------------------------------------//
	//         building components for alu_environment      //
	//         and object for alu_sequence                  //  
	//------------------------------------------------------//

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		alu_env = alu_environment::type_id::create("alu_environment", this);
		seq = alu_sequence::type_id::create("alu_seq");
	endfunction : build_phase

	//------------------------------------------------------//
	//       Printing the ALU architecture toptoplogy       //  
	//------------------------------------------------------//

	function void end_of_elaboration();
		uvm_top.print_topology();
	endfunction

	//------------------------------------------------------//
	//             running the test sequence                //  
	//------------------------------------------------------//

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//         reset and clock enable test                  //  
//------------------------------------------------------//

class rst_ce_test extends alu_test;

	`uvm_component_utils( rst_ce_test)
	rst_ce seq0;

	function new(string name = " rst_ce_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq0 = rst_ce ::type_id::create("alu_seq0");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq0.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//         single operand arithmatic test               //  
//------------------------------------------------------//

class single_operand_arithmatic_test extends alu_test;

	`uvm_component_utils( single_operand_arithmatic_test)
	single_operand_arithmatic seq1;

	function new(string name = " single_operand_arithmatic_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq1 = single_operand_arithmatic ::type_id::create("alu_seq1");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq1.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//         single operand logical test                  //  
//------------------------------------------------------//

class single_operand_logical_test extends alu_test;

	`uvm_component_utils( single_operand_logical_test)
	single_operand_logical seq2;

	function new(string name = " single_operand_logical_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq2 = single_operand_logical::type_id::create("alu_seq2");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq2.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//         two operand arithmatic test                  //  
//------------------------------------------------------//

class two_operand_arithmatic_test extends alu_test;

	`uvm_component_utils( two_operand_arithmatic_test)
	two_operand_arithmatic seq3;

	function new(string name = " two_operand_arithmatic_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq3 = two_operand_arithmatic ::type_id::create("alu_seq3");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq3.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//            two operand logical test                  //  
//------------------------------------------------------//

class two_operand_logical_test extends alu_test;

	`uvm_component_utils( two_operand_logical_test)
	two_operand_logical seq4;

	function new(string name = " two_operand_logical_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq4 = two_operand_logical::type_id::create("alu_seq4");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq4.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//      single operand arithmatic error test            //  
//------------------------------------------------------//

class single_operand_arithmatic_error_test extends alu_test;
	`uvm_component_utils( single_operand_arithmatic_error_test)
	single_operand_arithmatic_error seq5;
	function new(string name = " single_operand_arithmatic_error_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq5 = single_operand_arithmatic_error ::type_id::create("alu_seq5");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq5.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//      single operand logical error test               //  
//------------------------------------------------------//

class single_operand_logical_error_test extends alu_test;

	`uvm_component_utils( single_operand_logical_error_test)
	single_operand_logical_error seq6;

	function new(string name = " single_operand_logical_error_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq6 = single_operand_logical_error::type_id::create("alu_seq6");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq6.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//      two operand arithmatic error test               //  
//------------------------------------------------------//

class two_operand_arithmatic_error_test extends alu_test;

	`uvm_component_utils( two_operand_arithmatic_error_test)
	two_operand_arithmatic_error seq7;

	function new(string name = " two_operand_arithmatic_error_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq7 = two_operand_arithmatic_error ::type_id::create("alu_seq7");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq7.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//       two operand logical error test                 //  
//------------------------------------------------------//

class two_operand_logical_error_test extends alu_test;

	`uvm_component_utils( two_operand_logical_error_test)
	two_operand_logical_error seq8;

	function new(string name = " two_operand_logical_error_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq8 = two_operand_logical_error::type_id::create("alu_seq8");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq8.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//            rotate right error test                   //  
//------------------------------------------------------//

class rotate_right_error_test extends alu_test;

	`uvm_component_utils( rotate_right_error_test)
	rotate_right_error seq9;

	function new(string name = "rotate_right_error_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq9 = rotate_right_error::type_id::create("alu_seq9");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq9.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//            rotate left error test                    //  
//------------------------------------------------------//

class rotate_left_error_test extends alu_test;

	`uvm_component_utils( rotate_left_error_test)
	rotate_left_error seq10;

	function new(string name = "rotate_left_error_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq10 = rotate_left_error::type_id::create("alu_seq10");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq10.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);  
	endtask
endclass

//------------------------------------------------------//
//         16 clock cycle arithmatic test               //  
//------------------------------------------------------//

class cycle_16_arithmatic_test extends alu_test;

	`uvm_component_utils( cycle_16_arithmatic_test)
	cycle_16_arithmatic seq11;

	function new(string name = "cycle_16_arithmatic_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq11 = cycle_16_arithmatic::type_id::create("alu_seq11");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq11.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//         16 clock cycle logical test                  //  
//------------------------------------------------------//

class cycle_16_logical_test extends alu_test;

	`uvm_component_utils( cycle_16_logical_test)
	cycle_16_logical seq12;

	function new(string name = "cycle_16_logical_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq12 = cycle_16_logical::type_id::create("alu_seq12");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq12.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//           comparsion test for opa > opb,             //
//             opa < opb and opa = opb                  //  
//------------------------------------------------------//

class comparison_test extends alu_test;

	`uvm_component_utils( comparison_test)
	comparison seq13;

	function new(string name = "comparison_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq13 = comparison::type_id::create("alu_seq13");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq13.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
// invlaid cmd test for arithmatic and logical operation//  
//------------------------------------------------------//

class invalid_cmd_test extends alu_test;

	`uvm_component_utils( invalid_cmd_test)
	invalid_cmd seq14;

	function new(string name = "invalid_cmd_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq14 = invalid_cmd::type_id::create("alu_seq14");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq14.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//      16 clock cycle arithmatic error test            //  
//------------------------------------------------------//

class cycle_16_arithmatic_error_test extends alu_test;

	`uvm_component_utils( cycle_16_arithmatic_error_test)
	cycle_16_arithmatic_error seq15;

	function new(string name = "cycle_16_arithmatic_error_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq15 = cycle_16_arithmatic_error::type_id::create("alu_seq15");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq15.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//         16 clock cycle logical error test            //  
//------------------------------------------------------//

class cycle_16_logical_error_test extends alu_test;

	`uvm_component_utils( cycle_16_logical_error_test)
	cycle_16_logical_error seq16;

	function new(string name = "cycle_16_logical_error_test", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq16 = cycle_16_logical_error::type_id::create("alu_seq16");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq16.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass

//------------------------------------------------------//
//           alu regression sequence test               //  
//------------------------------------------------------//

class alu_regression_test extends alu_test;

	`uvm_component_utils(alu_regression_test)
	alu_regression reg_test;

	function new(string name = "alu_regression_test", uvm_component parent);
		super.new(name,parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		reg_test = alu_regression::type_id::create("reg_test");
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		reg_test.start(alu_env.alu_active_agt.alu_active_seqr);
		phase.drop_objection(this);
	endtask
endclass


