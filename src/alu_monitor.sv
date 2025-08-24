class alu_active_monitor extends uvm_monitor;

	// declaring interface handle for active monitor
	virtual alu_interface vif;

	// declaring the analysis port for active monitor
	uvm_analysis_port#(alu_sequence_item) active_mon_port;

	// declaring the alu_sequence_item class handle
	alu_sequence_item seq;

	// registering the alu_active_monitor component to the factory
	`uvm_component_utils(alu_active_monitor)

	//------------------------------------------------------//
	//  Creating a new constructor for alu_active_monitor   //  
	//------------------------------------------------------//

	function new (string name = "alu_active_monitor", uvm_component parent);
		super.new(name, parent);
		active_mon_port = new("active_mon_port", this);
	endfunction

	//------------------------------------------------------//
	//   building config_db in the alu_active_monitor       //  
	//------------------------------------------------------//

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq = alu_sequence_item::type_id::create("alu_seq");
		if(!uvm_config_db#(virtual alu_interface)::get(this, "", "vif", vif))
			`uvm_fatal("NOVIF",{"virtual interface must be set for:MONITOR INTERFACE ",get_full_name(),".vif"});
	endfunction

	//------------------------------------------------------//
	//    capturing the input signals from the interface    //  
	//------------------------------------------------------//

	task run_phase(uvm_phase phase);
		forever begin
			repeat(3) @(vif.alu_monitor_cb);
			if( (vif.alu_monitor_cb.cmd == 9 || vif.alu_monitor_cb.cmd == 10) && (vif.alu_monitor_cb.mode == 1) )
				repeat(1)@(vif.alu_monitor_cb);

			seq.rst       = vif.alu_monitor_cb.rst;
			seq.ce        = vif.alu_monitor_cb.ce;
			seq.mode      = vif.alu_monitor_cb.mode;
			seq.cin       = vif.alu_monitor_cb.cin;
			seq.cmd       = vif.alu_monitor_cb.cmd;
			seq.inp_valid = vif.alu_monitor_cb.inp_valid;
			seq.opa       = vif.alu_monitor_cb.opa;
			seq.opb       = vif.alu_monitor_cb.opb;
			active_mon_port.write(seq); 
		end
	endtask
endclass

class alu_passive_monitor extends uvm_monitor;

	// declaring interface handle for passive monitor
	virtual alu_interface vif;

	// declaring the analysis port for passive monitor
	uvm_analysis_port#(alu_sequence_item) passive_mon_port;

	// declaring the alu_sequence_item class handle
	alu_sequence_item seq;

	// registering the alu_passive_monitor component to the factory
	`uvm_component_utils(alu_passive_monitor)

	//------------------------------------------------------//
	//  Creating a new constructor for alu_passive_monitor  //  
	//------------------------------------------------------//

	function new (string name = "alu_passive_monitor", uvm_component parent);
		super.new(name, parent);
		passive_mon_port = new("passive_mon_port", this);
	endfunction

	//------------------------------------------------------//
	//   building config_db in the alu_passive_monitor      //  
	//------------------------------------------------------//

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seq = alu_sequence_item::type_id::create("alu_seq");
		if(!uvm_config_db#(virtual alu_interface)::get(this, "", "vif", vif))
			`uvm_fatal("NOVIF",{"virtual interface must be set for:MONITOR INTERFACE ",get_full_name(),".vif"});
	endfunction

	//------------------------------------------------------//
	//    capturing the output signals from the interface   //  
	//------------------------------------------------------//

	task run_phase(uvm_phase phase);
		forever begin
			repeat(3) @(vif.alu_monitor_cb);
			if( (vif.alu_monitor_cb.cmd == 9 || vif.alu_monitor_cb.cmd == 10) && (vif.alu_monitor_cb.mode == 1) )
				repeat(1)@(vif.alu_monitor_cb);

			seq.res       = vif.alu_monitor_cb.res;
			seq.err       = vif.alu_monitor_cb.err;
			seq.oflow     = vif.alu_monitor_cb.oflow;
			seq.cout      = vif.alu_monitor_cb.cout;
			seq.g         = vif.alu_monitor_cb.g;
			seq.l         = vif.alu_monitor_cb.l;
			seq.e         = vif.alu_monitor_cb.e;
			passive_mon_port.write(seq); 
		end
	endtask
endclass

