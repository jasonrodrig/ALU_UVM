class alu_sequence_item extends uvm_sequence_item;

	//------------------------------------------------------//
	//             randomized input signals                 //  
	//------------------------------------------------------//
	rand logic rst , ce , mode , cin;
	rand logic [`DATA_WIDTH - 1:0] opa , opb;
	rand logic [`CMD_WIDTH - 1:0] cmd;
	rand logic [1:0] inp_valid;

	//------------------------------------------------------//
	//          non randomized output signals               //  
	//------------------------------------------------------//

	logic [RESULT_WIDTH - 1 :0] res ;
	logic  err , oflow , cout , g , l , e;

	//------------------------------------------------------//
	//         registering input signals and output         //
	//                signals to the factory                //  
	//------------------------------------------------------//

	`uvm_object_utils_begin(alu_sequence_item)
	`uvm_field_int(rst,UVM_ALL_ON)
	`uvm_field_int(ce,UVM_ALL_ON)
	`uvm_field_int(mode,UVM_ALL_ON)
	`uvm_field_int(cin,UVM_ALL_ON)
	`uvm_field_int(cmd,UVM_ALL_ON)
	`uvm_field_int(inp_valid,UVM_ALL_ON)
	`uvm_field_int(opa,UVM_ALL_ON)
	`uvm_field_int(opb,UVM_ALL_ON)
	`uvm_field_int(res,UVM_ALL_ON)
	`uvm_field_int(err,UVM_ALL_ON)
	`uvm_field_int(oflow,UVM_ALL_ON)
	`uvm_field_int(cout,UVM_ALL_ON)
	`uvm_field_int(g,UVM_ALL_ON)
	`uvm_field_int(l,UVM_ALL_ON)
	`uvm_field_int(e,UVM_ALL_ON)
	`uvm_object_utils_end

	//------------------------------------------------------//
	//   Creating a new constructor for alu_sequence_item   //  
	//------------------------------------------------------//

	function new(string name = "alu_sequence_item");
		super.new(name);
	endfunction

endclass
