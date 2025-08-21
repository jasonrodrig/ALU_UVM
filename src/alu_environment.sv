class alu_environment extends uvm_env;
	alu_passive_agent alu_passive_agt;
	alu_active_agent  alu_active_agt;
	alu_scoreboard    alu_scb;
	alu_coverage      alu_cov;

	`uvm_component_utils(alu_environment)

	function new(string name = "alu_environment", uvm_component parent);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		alu_active_agt = alu_active_agent::type_id::create("alu_active_agent", this);
		alu_passive_agt = alu_passive_agent::type_id::create("alu_passive_agent", this);

    set_config_int("alu_active_agt","is_active",UVM_ACTIVE);
    set_config_int("alu_passive_agt","is_active",UVM_PASSIVE);
		alu_scb = alu_scoreboard::type_id::create("alu_scoreboard", this);
		alu_cov = alu_coverage::type_id::create("alu_coverage", this);
	endfunction

	function void connect_phase(uvm_phase phase);
		alu_passive_agt.alu_passive_mon.mon_port.connect(alu_scb.mon_scb_port);
		alu_active_agt.alu_active_driv.driv_port.connect(alu_scb.driv_scb_port);
		alu_passive_agt.alu_passive_mon.mon_port.connect(alu_cov.cov_mon_port);
		alu_active_agt.alu_active_driv.driv_port.connect(alu_cov.cov_driv_port);
	endfunction

endclass


