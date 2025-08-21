typedef enum{ADD,SUB,ADD_CIN,SUB_CIN,INC_A,DEC_A,INC_B,DEC_B,CMP,SH_MUL,ADD_MUL}arith;
typedef enum{AND,NAND,OR,NOR,XOR,XNOR,NOT_A,NOT_B,SHR1_A,SHL1_A,SHR1_B,SHL1_B,ROL_A_B,ROR_A_B}logical;

class alu_active_monitor extends uvm_monitor;

	virtual alu_interface vif;

	uvm_analysis_port #(alu_sequence_item) active_mon_port;

	alu_sequence_item seq;

	`uvm_component_utils(alu_active_monitor)

	function new (string name = "alu_active_monitor", uvm_component parent);
		super.new(name, parent);
		active_mon_port = new("active_mon_port", this);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq = alu_sequence_item::type_id::create("alu_seq");
		if(!uvm_config_db#(virtual alu_interface)::get(this, "", "vif", vif))
			`uvm_fatal("NOVIF",{"virtual interface must be set for:MONITOR INTERFACE ",get_full_name(),".vif"});
	endfunction

	task run_phase(uvm_phase phase);
		forever begin
			repeat(3) @(vif.alu_monitor_cb);

			if( (vif.alu_monitor_cb.cmd == 9 || vif.alu_monitor_cb.cmd == 10) && (vif.alu_monitor_cb.mode == 1) )
			begin
				repeat(1)@(vif.alu_monitor_cb);
			end
			seq.rst       = vif.alu_monitor_cb.rst;
			seq.ce        = vif.alu_monitor_cb.ce;
			seq.mode      = vif.alu_monitor_cb.mode;
			seq.cin       = vif.alu_monitor_cb.cin;
			seq.cmd       = vif.alu_monitor_cb.cmd;
			seq.inp_valid = vif.alu_monitor_cb.inp_valid;
			seq.opa       = vif.alu_monitor_cb.opa;
			seq.opb       = vif.alu_monitor_cb.opb;
	/*  
			seq.res       = vif.alu_monitor_cb.res;
			seq.err       = vif.alu_monitor_cb.err;
			seq.oflow     = vif.alu_monitor_cb.oflow;
			seq.cout      = vif.alu_monitor_cb.cout;
			seq.g         = vif.alu_monitor_cb.g;
			seq.l         = vif.alu_monitor_cb.l;
			seq.e         = vif.alu_monitor_cb.e;
		*/	
			if(vif.alu_monitor_cb.mode)
			begin
			$display("Monitor @ %0t \n RST = %b | CE = %b | MODE = %b | CMD = %0s | INP_VALID = %d | CIN = %b | OPA = %d | OPB = %d |",
				$time, vif.alu_monitor_cb.rst , vif.alu_monitor_cb.ce , vif.alu_monitor_cb.mode , arith'(vif.alu_monitor_cb.cmd), vif.alu_monitor_cb.inp_valid, vif.alu_monitor_cb.cin , vif.alu_monitor_cb.opa , vif.alu_monitor_cb.opb );
			end
			else begin
			$display("Monitor @ %0t \n RST = %b | CE = %b | MODE = %b | CMD = %0s | INP_VALID = %d | CIN = %b | OPA = %d | OPB = %d |",
				$time, vif.alu_monitor_cb.rst , vif.alu_monitor_cb.ce , vif.alu_monitor_cb.mode , logical'(vif.alu_monitor_cb.cmd) , vif.alu_monitor_cb.inp_valid, vif.alu_monitor_cb.cin , vif.alu_monitor_cb.opa , vif.alu_monitor_cb.opb );
			end
		/*	$display("Monitor @ %0t \n RES = %d | OFLOW = %b | COUT = %b | G = %b | L = %b | E = %b | ERR = %b |",
				$time, vif.alu_monitor_cb.res , vif.alu_monitor_cb.oflow , vif.alu_monitor_cb.cout , vif.alu_monitor_cb.g , vif.alu_monitor_cb.l , 									  	  vif.alu_monitor_cb.e , vif.alu_monitor_cb.err );
		*/	active_mon_port.write(seq); 
		end
	endtask

endclass

class alu_passive_monitor extends uvm_monitor;

	virtual alu_interface vif;

	uvm_analysis_port #(alu_sequence_item) passive_mon_port;

	alu_sequence_item seq;

	`uvm_component_utils(alu_passive_monitor)

	function new (string name = "alu_passive_monitor", uvm_component parent);
		super.new(name, parent);
		passive_mon_port = new("passive_mon_port", this);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq = alu_sequence_item::type_id::create("alu_seq");
		if(!uvm_config_db#(virtual alu_interface)::get(this, "", "vif", vif))
			`uvm_fatal("NOVIF",{"virtual interface must be set for:MONITOR INTERFACE ",get_full_name(),".vif"});
	endfunction

	task run_phase(uvm_phase phase);
		forever begin
			repeat(3) @(vif.alu_monitor_cb);

			if( (vif.alu_monitor_cb.cmd == 9 || vif.alu_monitor_cb.cmd == 10) && (vif.alu_monitor_cb.mode == 1) )
			begin
				repeat(1)@(vif.alu_monitor_cb);
			end

		/*seq.ce        = vif.alu_monitor_cb.ce;
			seq.mode      = vif.alu_monitor_cb.mode;
			seq.cin       = vif.alu_monitor_cb.cin;
			seq.cmd       = vif.alu_monitor_cb.cmd;
			seq.inp_valid = vif.alu_monitor_cb.inp_valid;
			seq.opa       = vif.alu_monitor_cb.opa;
			seq.opb       = vif.alu_monitor_cb.opb;
		*/
			seq.res       = vif.alu_monitor_cb.res;
			seq.err       = vif.alu_monitor_cb.err;
			seq.oflow     = vif.alu_monitor_cb.oflow;
			seq.cout      = vif.alu_monitor_cb.cout;
			seq.g         = vif.alu_monitor_cb.g;
			seq.l         = vif.alu_monitor_cb.l;
			seq.e         = vif.alu_monitor_cb.e;
			/*$display("Monitor @ %0t \n RST = %b | CE = %b | MODE = %b | CMD = %d | INP_VALID = %d | CIN = %b | OPA = %d | OPB = %d |",
				$time, vif.alu_monitor_cb.rst , vif.alu_monitor_cb.ce , vif.alu_monitor_cb.mode , vif.alu_monitor_cb.cmd , vif.alu_monitor_cb.inp_valid , 								  vif.alu_monitor_cb.cin , vif.alu_monitor_cb.opa , vif.alu_monitor_cb.opb );
			*/
			$display("Monitor @ %0t \n RES = %d | OFLOW = %b | COUT = %b | G = %b | L = %b | E = %b | ERR = %b |",
				$time, vif.alu_monitor_cb.res , vif.alu_monitor_cb.oflow , vif.alu_monitor_cb.cout , vif.alu_monitor_cb.g , vif.alu_monitor_cb.l , vif.alu_monitor_cb.e , vif.alu_monitor_cb.err );
			passive_mon_port.write(seq); 
		end
	endtask

endclass

