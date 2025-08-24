class alu_active_agent extends uvm_agent;
	
	// declaring the handles for alu_driver , alu_sequencer , alu_active_monitor
	alu_driver          alu_active_driv;
	alu_sequencer       alu_active_seqr;
	alu_active_monitor  alu_active_mon;

	// registering the alu_active_agent component to the factory
	`uvm_component_utils(alu_active_agent)

	//------------------------------------------------------//
	//  Creating a new constructor for alu_active_agent     //  
	//------------------------------------------------------//

	function new (string name = "alu_active_agent", uvm_component parent);
		super.new(name, parent);
	endfunction 

	//------------------------------------------------------//
	//       building alu_driver, alu_sequencer and         //
	//            alu_active_monitor component              //  
	//------------------------------------------------------//

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if(get_is_active() == UVM_ACTIVE) begin
			alu_active_driv = alu_driver::type_id::create("alu_active_driv", this);
			alu_active_seqr = alu_sequencer::type_id::create("alu_active_seqr", this);
		end
		  alu_active_mon = alu_active_monitor::type_id::create("alu_active_mon", this);
	endfunction

	//------------------------------------------------------//
	//         Connecting 2 component between alu_driver    //
	//                   and alu_sequencer                  //  
	//------------------------------------------------------//

	function void connect_phase(uvm_phase phase);
		if(get_is_active() == UVM_ACTIVE) begin
			alu_active_driv.seq_item_port.connect(alu_active_seqr.seq_item_export);
		end
	endfunction
endclass  

class alu_passive_agent extends uvm_agent;
  // declaring the handle for alu_passive_monitor
	alu_passive_monitor alu_passive_mon;

	// registering the alu_passive_agent component to the factory	
	`uvm_component_utils(alu_passive_agent)

	//------------------------------------------------------//
	//  Creating a new constructor for alu_passive_agent    //  
	//------------------------------------------------------//

	function new(string name = "alu_passive_agent", uvm_component parent = null);
		super.new(name, parent);
	endfunction 

	//------------------------------------------------------//
	//       building alu_passive_monitor component         //  
	//------------------------------------------------------//

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if(get_is_active() == UVM_PASSIVE) begin	
			alu_passive_mon = alu_passive_monitor::type_id::create("alu_passive_mon", this);
		end
	endfunction
endclass  

