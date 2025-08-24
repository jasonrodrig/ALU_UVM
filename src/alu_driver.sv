class alu_driver extends uvm_driver #(alu_sequence_item);

	// declaring interface handle
	virtual alu_interface vif;

	// registering the alu_driver to the factory
	`uvm_component_utils(alu_driver)

	//------------------------------------------------------//
	//    Creating a new constructor for alu_driver         //  
	//------------------------------------------------------//

	function new (string name = "alu_driver", uvm_component parent);
		super.new(name, parent);
	endfunction : new

	//------------------------------------------------------//
	//         building config_db in the alu_driver         //  
	//------------------------------------------------------//

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if(!uvm_config_db#(virtual alu_interface)::get(this,"","vif", vif))
			`uvm_fatal("NO_VIF",{"virtual interface must be set for: ALU_DRIVER ",get_full_name(),".vif"});
	endfunction

	//------------------------------------------------------//
	//                Running the driver                    //  
	//------------------------------------------------------//

	task run_phase(uvm_phase phase);
		forever begin  
			seq_item_port.get_next_item(req);
			alu_driver_code();   
			seq_item_port.item_done();
		end
	endtask

	//------------------------------------------------------//
	//                   Driver code                        //  
	//------------------------------------------------------//

	task alu_driver_code();

		// checking if input valid is 1 or 2
		if( req.inp_valid == 1 || req.inp_valid == 2 )
		begin

			// check if the alu selected is arithmatic and single operand operation
			if( req.mode == 1 && req.cmd inside{4,5,6,7} )
				drive_signals();

			// check if the alu selected is logical and single operand operation
			else if( req.mode == 0 && req.cmd inside{6,7,8,9,10,11} )
				drive_signals();

			// if the input valid is 1 or 2 and still it is not an single operand operation on
			// both arithematic and logical then perform the 16 cycle operation until input valid 
			// is 3 or when count is 15
			else 
			begin
				for( int i = 0; i < 16; i++ ) 
				begin
					// disable randomized signals for rst , ce , mode and cmd
					req.rst.rand_mode(0);
					req.ce.rand_mode(0);       
					req.mode.rand_mode(0);
					req.cmd.rand_mode(0);
					void'( req.randomize() );

					// if count is 15 then drive the input signal
					if( i == 15 )
					begin
						req.mode.rand_mode(1);
						req.cmd.rand_mode(1);
						drive_signals();
					end
					else 
					begin
						//if inp_valid is 3 then drive the input signals
						if( req.inp_valid == 3 )
						begin
							i = 0 ;
							drive_signals();
							break;
						end
						// keep on driving the input signals until 
						// input valid is 3 or count = 15 is reached
						else
						begin
							drive_signals(); 
							delay();
						end
					end
				end
			end
			delay();     
		end

		// if input valid is 3, then drive the signals 
		else
		begin
			if( req.inp_valid == 0 || req.inp_valid == 3 )
				drive_signals();
			delay();
		end
	endtask 

	//------------------------------------------------------//
	//            Driving the input signals                 //  
	//------------------------------------------------------//

	task drive_signals();
		vif.alu_driver_cb.rst       <= req.rst;
		vif.alu_driver_cb.ce        <= req.ce;
		vif.alu_driver_cb.mode      <= req.mode;
		vif.alu_driver_cb.cin       <= req.cin;
		vif.alu_driver_cb.cmd       <= req.cmd;
		vif.alu_driver_cb.inp_valid <= req.inp_valid;
		vif.alu_driver_cb.opa       <= req.opa;
		vif.alu_driver_cb.opb       <= req.opb;
	endtask

	//------------------------------------------------------//
	//   give certain amount of delay for next transaction  //  
	//------------------------------------------------------//

	task delay();
		if( ( req.mode == 1 ) && ( req.cmd == 9 || req.cmd == 10 ) )
			repeat(4) @(vif.alu_driver_cb);  
		else
			repeat(3) @(vif.alu_driver_cb); 
	endtask

endclass
