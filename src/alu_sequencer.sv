class alu_sequencer extends uvm_sequencer#(alu_sequence_item);
	//------------------------------------------------------//
	// Registering the alu_sequencer componenet to factory  //  
	//------------------------------------------------------//

	`uvm_component_utils(alu_sequencer)

	//------------------------------------------------------//
	//    Creating a new constructor for alu_driver         //  
	//------------------------------------------------------//

	function new(string name, uvm_component parent);
		super.new(name,parent);
	endfunction

endclass
