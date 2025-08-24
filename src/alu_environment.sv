class alu_environment extends uvm_env;

	// declaring handle for alu_active_agent, alu_passive_agent,
	// alu_scoreboard and alu_coverage
	alu_passive_agent alu_passive_agt;
	alu_active_agent  alu_active_agt;
	alu_scoreboard    alu_scb;
	alu_coverage      alu_cov;

	// registering the alu_component to the factory
	`uvm_component_utils(alu_environment)

	//------------------------------------------------------//
	//  Creating a new constructor for alu_environment      //  
	//------------------------------------------------------//

	function new(string name = "alu_environment", uvm_component parent);
		super.new(name, parent);
	endfunction

	//------------------------------------------------------//
	//       building component for alu_active_agent,       //
	//  alu_passive_agent, alu_scoreboard and alu_coverage  //  
	//------------------------------------------------------//

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		alu_active_agt  = alu_active_agent::type_id::create("alu_active_agt", this);
		alu_passive_agt = alu_passive_agent::type_id::create("alu_passive_agt", this);
		alu_scb = alu_scoreboard::type_id::create("alu_scoreboard", this);
		alu_cov = alu_coverage::type_id::create("alu_coverage", this);
		set_config_int("alu_active_agt","is_active",UVM_ACTIVE);
		set_config_int("alu_passive_agt","is_active",UVM_PASSIVE);
	endfunction

	//------------------------------------------------------//
	//            Connecting 2 component:                   //
	//  1 ) alu_active_monitor to alu_scoreboard            //
	//  2 ) alu_active_monitor to alu_coverage              // 
	//  3 ) alu_passive_monitor to alu_scoreboard           //
	//  4 ) alu_passive_monitor to alu_coverage             //
	//------------------------------------------------------//

	function void connect_phase(uvm_phase phase);
		alu_active_agt.alu_active_mon.active_mon_port.connect(alu_scb.active_scb_port);
		alu_active_agt.alu_active_mon.active_mon_port.connect(alu_cov.cov_active_mon_port);
		alu_passive_agt.alu_passive_mon.passive_mon_port.connect(alu_scb.passive_scb_port);	
		alu_passive_agt.alu_passive_mon.passive_mon_port.connect(alu_cov.cov_passive_mon_port);
	endfunction
endclass


