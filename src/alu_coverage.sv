`uvm_analysis_imp_decl(_active_mon_cg)
`uvm_analysis_imp_decl(_passive_mon_cg)

class alu_coverage extends uvm_component;
	`uvm_component_utils(alu_coverage)

	uvm_analysis_imp_active_mon_cg#(alu_sequence_item, alu_coverage) cov_active_mon_port;
	uvm_analysis_imp_passive_mon_cg#(alu_sequence_item, alu_coverage) cov_passive_mon_port;
	
	alu_sequence_item active_mon, passive_mon;
	real active_mon_cov_results, passive_mon_cov_results;

	covergroup input_coverage;
		option.per_instance = 1;
		
		opb       : coverpoint active_mon.opb { bins opb = {[0:255]} with (item / 32 ); }
		cmd       : coverpoint active_mon.cmd { 
		                         bins arithmatic_cmd[] = {[0:10]} iff (active_mon.mode == 1'b1);
                             bins logical_cmd[]    = {[0:13]} iff (active_mon.mode == 1'b0);
			                       ignore_bins invalid_arith_cmd[] = {11,12,13,14,15} iff(active_mon.mode == 1'b1);
                             ignore_bins invalid_logic_cmd[] = {14,15} iff(active_mon.mode == 1'b0);
		                                        }
		inp_valid   : coverpoint active_mon.inp_valid { bins inp_valid[]  = {0,1,2,3}; }
		cin         : coverpoint active_mon.cin       { bins cin[]        = {0,1}; }
		mode        : coverpoint active_mon.mode      { bins mode[]       = {0,1}; } 
		ce          : coverpoint active_mon.ce        { bins ce[]         = {0,1}; }
		rst         : coverpoint active_mon.rst       { bins rst[]        = {0,1}; }
		rstXce        : cross rst , ce ; 
		ceXmode       : cross ce , mode;
		inp_validXmode: cross inp_valid , mode;
		modeXcmd      : cross mode , cmd {
			bins add              = binsof(cmd) intersect{0}  && binsof(mode) intersect{1};
			bins sub              = binsof(cmd) intersect{1}  && binsof(mode) intersect{1};
			bins add_cin          = binsof(cmd) intersect{2}  && binsof(mode) intersect{1};
			bins sub_cin          = binsof(cmd) intersect{3}  && binsof(mode) intersect{1};
			bins inc_A            = binsof(cmd) intersect{4}  && binsof(mode) intersect{1};
			bins dec_A            = binsof(cmd) intersect{5}  && binsof(mode) intersect{1};
			bins inc_B            = binsof(cmd) intersect{6}  && binsof(mode) intersect{1};
			bins dec_B            = binsof(cmd) intersect{7}  && binsof(mode) intersect{1};
			bins compare          = binsof(cmd) intersect{8}  && binsof(mode) intersect{1};
			bins inc_mul          = binsof(cmd) intersect{9}  && binsof(mode) intersect{1};
			bins shift_mul        = binsof(cmd) intersect{10} && binsof(mode) intersect{1};
			bins and_op           = binsof(cmd) intersect{0}  && binsof(mode) intersect{0};
			bins nand_op          = binsof(cmd) intersect{1}  && binsof(mode) intersect{0};
			bins or_op            = binsof(cmd) intersect{2}  && binsof(mode) intersect{0};
			bins nor_op           = binsof(cmd) intersect{3}  && binsof(mode) intersect{0};
			bins xor_op           = binsof(cmd) intersect{4}  && binsof(mode) intersect{0};
			bins xnor_op          = binsof(cmd) intersect{5}  && binsof(mode) intersect{0};
			bins notA_op          = binsof(cmd) intersect{6}  && binsof(mode) intersect{0};
			bins notB_op          = binsof(cmd) intersect{7}  && binsof(mode) intersect{0};
			bins shift_right_A_op = binsof(cmd) intersect{8}  && binsof(mode) intersect{0};
			bins shift_left_A_op  = binsof(cmd) intersect{9}  && binsof(mode) intersect{0};
			bins shift_right_B_op = binsof(cmd) intersect{10} && binsof(mode) intersect{0};
			bins shift_left_B_op  = binsof(cmd) intersect{11} && binsof(mode) intersect{0};
			bins rotate_left_op   = binsof(cmd) intersect{12} && binsof(mode) intersect{0};
			bins rotate_right_op  = binsof(cmd) intersect{13} && binsof(mode) intersect{0}; 
		}
	endgroup

	covergroup output_coverage;
		option.per_instance = 1;
		result : coverpoint passive_mon.res  { bins res_bins     = {[0:512]} with (item / 64); }
		oflow  : coverpoint passive_mon.oflow{ bins oflow[]      = {0,1}; }
		cout   : coverpoint passive_mon.cout { bins cout[]       = {0,1}; }
		err    : coverpoint passive_mon.err  { bins err[]        = {0,1}; }
		g      : coverpoint passive_mon.g    { bins g[]          = {0,1}; } 
		l      : coverpoint passive_mon.l    { bins l[]          = {0,1}; }
		e      : coverpoint passive_mon.e    { bins e[]          = {0,1}; } 
	endgroup

	function new(string name = "alu_coverage", uvm_component parent);
		super.new(name, parent);
		output_coverage = new();
		input_coverage  = new();
		cov_active_mon_port    = new("cov_active_mon_port", this);
		cov_passive_mon_port   = new("cov_passive_mon_port", this);
	endfunction

	function void write_active_mon_cg(alu_sequence_item active_mon_seq);
		active_mon = active_mon_seq;
		input_coverage.sample();
	endfunction

	function void write_passive_mon_cg(alu_sequence_item passive_mon_seq);
		passive_mon = passive_mon_seq;
		output_coverage.sample();
	endfunction

	function void extract_phase(uvm_phase phase);
		super.extract_phase(phase);
		active_mon_cov_results   = input_coverage.get_coverage();
		passive_mon_cov_results  = output_coverage.get_coverage();
	endfunction

	function void report_phase(uvm_phase phase);
		super.report_phase(phase);
		`uvm_info(get_type_name, $sformatf("[ACTIVE_MONITOR] Coverage ------> %0.2f%%,", active_mon_cov_results), UVM_MEDIUM);
		`uvm_info(get_type_name, $sformatf("[PASSIVE_MONITOR] Coverage ------> %0.2f%%", passive_mon_cov_results), UVM_MEDIUM);
	endfunction
endclass
