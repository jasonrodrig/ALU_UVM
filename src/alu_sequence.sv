

class alu_sequence extends uvm_sequence#(alu_sequence_item);

	`uvm_object_utils(alu_sequence)
	function new(string name = "alu_sequence");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items)begin
			req = alu_sequence_item::type_id::create("req");
			wait_for_grant();
			void'(req.randomize());
			send_request(req);
			wait_for_item_done();
			$display("unblocked");
		end
	endtask
endclass

class rst_ce extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(rst_ce)

	function new(string name = "rst_ce");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst dist{ 0:=4 , 1:=2};
					req.ce  dist{ 1:=4 , 0:=2};
				}
			)
		end
	endtask
endclass 

class single_operand_arithmatic extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(single_operand_arithmatic)

	function new(string name = "single_operand_arithmatic");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 1;
					req.inp_valid inside {[1:2]};
					req.cmd inside {[4:7]};
				}
			)
		end
	endtask
endclass 

class single_operand_logical extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(single_operand_logical)

	function new(string name = "single_operand_logical");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 0;
					req.inp_valid inside {[1:2]};
					req.cmd inside {[6:11]};
				}
			)
		end
	endtask
endclass 

class two_operand_arithmatic extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(two_operand_arithmatic)

	function new(string name = "two_operand_arithmatic");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 1;
					req.inp_valid == 3;
					req.cmd inside {[0:3],[8:10]};
				}
			)
		end
	endtask
endclass 

class two_operand_logical extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(two_operand_logical)

	function new(string name = "two_operand_logical");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 0;
					req.inp_valid == 3;
					req.cmd inside {[0:5],[12:13]};
				}
			)
		end
	endtask
endclass 

class single_operand_arithmatic_error extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(single_operand_arithmatic_error)

	function new(string name = "single_operand_arithmatic_error");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 1;
					req.inp_valid inside { 0 , 3 };
					req.cmd inside {[4:7]};
				}
			)
		end
	endtask
endclass 

class single_operand_logical_error extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(single_operand_logical_error)

	function new(string name = "single_operand_logical_error");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 0;
					req.inp_valid inside { 0 , 3 };
					req.cmd inside {[6:11]};
				}
			)
		end
	endtask
endclass 

class two_operand_arithmatic_error extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(two_operand_arithmatic_error)

	function new(string name = "two_operand_arithmatic_error");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 1;
					req.inp_valid == 0;
					req.cmd inside {[0:3],[8:10]};
				}
			)
		end
	endtask
endclass 

class two_operand_logical_error extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(two_operand_logical_error)

	function new(string name = "two_operand_logical_error");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 0;
					req.inp_valid == 0;
					req.cmd inside {[0:5],[12:13]};
				}
			)
		end
	endtask
endclass 

class rotate_right_error extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(rotate_right_error)

	function new(string name = "rotate_right_error");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 0;
					req.inp_valid == 3;
					req.cmd == 13;
					req.opa == 1 ;
					req.opb inside {[8:255]};
				}
			)
		end
	endtask
endclass 

class rotate_left_error extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(rotate_left_error)

	function new(string name = "rotate_left_error");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 0;
					req.inp_valid == 3;
					req.cmd == 12;
					req.opa == 1 ;
					req.opb inside {[8:255]};
				}
			)
		end
	endtask
endclass 

class cycle_16_arithmatic extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(cycle_16_arithmatic)

	function new(string name = "cycle_16_arithmatic");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 1;
					req.inp_valid inside {[1:2]};
					req.cmd inside {[0:3],[8:10]};
				}
			)
		end
	endtask
endclass 

class cycle_16_logical extends uvm_sequence#(alu_sequence_item);
	`uvm_object_utils(cycle_16_logical)

	function new(string name = "cycle_16_logical");
		super.new(name);
	endfunction

	task body();
		repeat(`no_of_items) begin
			`uvm_do_with( 
				req,
				{ 
					req.rst == 0;
					req.ce == 1;
					req.mode == 0;
					req.inp_valid inside {[1:2]};
					req.cmd inside {[0:5],[12:13]};
				}
			)
		end
	endtask
endclass 

class alu_regression extends uvm_sequence#(alu_sequence_item);

	`uvm_object_utils(alu_regression)
	rst_ce seq0;

	single_operand_arithmatic seq1;
	single_operand_logical    seq2;
	two_operand_arithmatic    seq3;
	two_operand_logical       seq4;

	single_operand_arithmatic_error seq5;
	single_operand_logical_error    seq6;
	two_operand_arithmatic_error    seq7;
	two_operand_logical_error       seq8;

	rotate_right_error  seq9;
	rotate_left_error   seq10;

	cycle_16_arithmatic seq11;
	cycle_16_logical    seq12;

	function new(string name = "alu_regression");
		super.new(name);
	endfunction

	task body();
		`uvm_do(seq0)
		`uvm_do(seq1)
		`uvm_do(seq2)
		`uvm_do(seq3)         
		`uvm_do(seq4)
		`uvm_do(seq5)
		`uvm_do(seq6)
		`uvm_do(seq7)         
		`uvm_do(seq8) 
		`uvm_do(seq9)         
		`uvm_do(seq10)
		`uvm_do(seq11)         
		`uvm_do(seq12) 
	endtask
endclass
