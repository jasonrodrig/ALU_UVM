//TLM DECL Ports
`uvm_analysis_imp_decl(_active_mon_scb)
`uvm_analysis_imp_decl(_passive_mon_scb)

class alu_scoreboard extends uvm_scoreboard;
	// handle decleration for alu_sequnce item using queues
	alu_sequence_item active_mon_queue[$];
	alu_sequence_item passive_mon_queue[$];

	// monitor and reference results declaration for comparsion only
	logic [(RESULT_WIDTH - 1 ) + 6:0] monitor_results;
	logic [(RESULT_WIDTH - 1 ) + 6:0] reference_results;

	// mimicing the multiplication funactionlaity using register 	
	reg [RESULT_WIDTH - 1:0] t_mul;

	// declration for temporary reference outputs
	logic [RESULT_WIDTH - 1:0] ref_res ;
	logic  ref_err , ref_oflow , ref_cout , ref_g , ref_l , ref_e;

	// registering the alu_scoareboard to the factory	
	`uvm_component_utils(alu_scoreboard)

	// analysis import declaration for both active_monitor and passive_monitor	
	uvm_analysis_imp_active_mon_scb#(alu_sequence_item, alu_scoreboard) active_scb_port;
	uvm_analysis_imp_passive_mon_scb#(alu_sequence_item, alu_scoreboard) passive_scb_port;

	//------------------------------------------------------//
	//     Creating New constructor for alu_scoreboard      //   
	//------------------------------------------------------//

	function new(string name = "alu_scoreboard", uvm_component parent);
		super.new(name, parent);
		active_scb_port  = new("active_scb_port" , this);
		passive_scb_port = new("passive_scb_port", this); 
	endfunction

	//------------------------------------------------------//
	//      Captures the passive monitor transaction and    //
	// temporary storing the outputs in the packet_1 queue  //   
	//------------------------------------------------------//

	function void write_passive_mon_scb(alu_sequence_item packet_1);
		passive_mon_queue.push_back(packet_1);
	endfunction

	//------------------------------------------------------//
	//      Captures the active monitor transaction and     //
	//   temporary storing the inputs in the packet_2 queue //   
	//------------------------------------------------------//

	function void write_active_mon_scb(alu_sequence_item packet_2);
		active_mon_queue.push_back(packet_2);
	endfunction

	//------------------------------------------------------//
	// Running the alu_reference model and comparison report//
	//------------------------------------------------------//

	task run_phase(uvm_phase phase);
		forever begin
			fork
				begin
					// waiting when the passive_mon_queue has the transaction stored in the
					// queue and perform the extraction of outputs from the passive monitor
					wait(passive_mon_queue.size() > 0);
					extract_outputs_from_passive_monitor();
				end
				begin
					// waiting when the active_mon_queue has the transaction stored in the
					// queue and perform the extraction of inputs from the active monitor 
					wait(active_mon_queue.size() > 0);
					extract_inputs_from_active_monitor();
				end
			join
			// generate the comparsion report by comparing reference results 
			// and monitor results and displaying the test pass or fail
			comparision_report();
		end
	endtask

	//------------------------------------------------------//
	//           performs extraction of output bits         //
	//               from the passive monitor               //
	//------------------------------------------------------//

	task extract_outputs_from_passive_monitor();
		alu_sequence_item packet_4;
		packet_4 = passive_mon_queue.pop_front();
		$display(" Monitor output : @ %0t \n RES = %d | OFLOW = %b | COUT = %b | G = %b | L = %b | E = %b | ERR = %b |",$time, packet_4.res , packet_4.oflow , packet_4.cout , packet_4.g , packet_4.l, packet_4.e , packet_4.err );
		monitor_results = { packet_4.res, packet_4.oflow, packet_4.cout, packet_4.g, packet_4.l, packet_4.e, packet_4.err };
		$display(" time : %t | monitor_results_stored   = %b", $time, monitor_results);
	endtask

	//------------------------------------------------------//
	//           performs extraction of input bits          //
	//               from the active monitor                //
	//------------------------------------------------------//

	task extract_inputs_from_active_monitor();
		alu_sequence_item packet_3;
		packet_3 = active_mon_queue.pop_front();
		$display(" Monitor input : @ %0t \n RST = %b | CE = %b | MODE = %b | CMD = %d | INP_VALID = %d | CIN = %b | OPA = %d | OPB = %d ", $time, packet_3.rst , packet_3.ce , packet_3.mode , packet_3.cmd , packet_3.inp_valid , packet_3.cin , packet_3.opa , packet_3.opb );
		alu_reference_model(packet_3);
	endtask

	//------------------------------------------------------//
	//         performs the alu reference model by          //
	//             mimicing its functionlaity               //
	//------------------------------------------------------//

	task alu_reference_model(input alu_sequence_item packet_3);

		// reset condition
		if(packet_3.rst == 1 )begin
			ref_res = 'bz ;
			ref_oflow = 'bz; 
			ref_cout = 'bz;
			ref_g = 'bz ; 
			ref_l = 'bz; 
			ref_e = 'bz; 
			ref_err = 'bz;
		end

		// clock enable condition
		else if(packet_3.ce)begin
			ref_res ='bz ;
			ref_oflow = 'bz; 
			ref_cout = 'bz;
			ref_g = 'bz ; 
			ref_l = 'bz; 
			ref_e = 'bz; 
			ref_err = 'bz;
			t_mul = 'b0;

			if( packet_3.mode )
				//Arithematic Operation
				arithematic_operation(packet_3);
			else
				//Logical Opertion
				logical_operation(packet_3);
		end
		$display(" Reference output : @ %0t \n RES = %d | OFLOW = %b | COUT = %b | G = %b | L = %b | E = %b | ERR = %b |",$time, ref_res , ref_oflow , ref_cout , ref_g , ref_l, ref_e , ref_err );
		reference_results = { ref_res, ref_oflow, ref_cout, ref_g, ref_l, ref_e, ref_err };
		$display(" time : %t | reference_results_stored = %b", $time, reference_results); 
	endtask

	//------------------------------------------------------//
	//         performs the arithmatic operation            //
	//------------------------------------------------------//

	task arithematic_operation(input alu_sequence_item packet_3);
		case(packet_3.cmd)

			0:begin // ADD WITHOUT CIN
				if( packet_3.inp_valid == 3) 
				begin
					ref_res = packet_3.opa + packet_3.opb;
					ref_cout = ( ref_res[`DATA_WIDTH] ) ? 1 : 0;
				end
				else ref_err = 1;
			end

			1:begin // SUB WITHOUT CIN
				if( packet_3.inp_valid == 3) 
				begin
					ref_res = ( packet_3.opa - packet_3.opb ) & ( { { (`DATA_WIDTH){1'b0} } , { (`DATA_WIDTH){1'b1} } } );
					ref_oflow = ( ( packet_3.opa < packet_3.opb ) || ( ( packet_3.opa == packet_3.opb ) && ( packet_3.cin == 1 ) ) ) ? 1 :0;
				end
				else ref_err = 1;
			end

			2:begin // ADD WITH CIN
				if( packet_3.inp_valid == 3) 
				begin
					ref_res = packet_3.opa + packet_3.opb + packet_3.cin;
					ref_cout = ( ref_res[`DATA_WIDTH] ) ? 1 : 0;
				end
				else ref_err = 1;
			end

			3:begin // SUB WITH CIN
				if( packet_3.inp_valid == 3) 
				begin
					ref_res = ( packet_3.opa - packet_3.opb - packet_3.cin ) & ( { { (`DATA_WIDTH){1'b0} } , { (`DATA_WIDTH){1'b1} } } );
					ref_oflow = ( ( packet_3.opa < packet_3.opb ) || ( ( packet_3.opa == packet_3.opb ) && ( packet_3.cin == 1 ) ) ) ? 1 :0;
				end
				else ref_err = 1;
			end

			4:begin // INCREMENT A
				if( packet_3.inp_valid == 1)
				begin
					ref_res = packet_3.opa + 1;
					ref_cout = ( ref_res[`DATA_WIDTH] ) ? 1 : 0;
				end
				else ref_err = 1;
			end

			5:begin // DECREMENT A
				if( packet_3.inp_valid == 1)
				begin
					ref_res = ( packet_3.opa - 1 ) & ( { { (`DATA_WIDTH){1'b0} } , { (`DATA_WIDTH){1'b1} } } );
					ref_oflow = ( packet_3.opa == 0 ) ? 1 : 0;
				end
				else ref_err = 1;
			end

			6:begin // INCREMENT B
				if( packet_3.inp_valid == 2)
				begin
					ref_res = packet_3.opb + 1;
					ref_cout = ( ref_res[`DATA_WIDTH] ) ? 1 : 0;
				end
				else ref_err = 1;
			end

			7:begin // DECREMENT B
				if( packet_3.inp_valid == 2)
				begin
					ref_res = ( packet_3.opb - 1 ) & ( { { (`DATA_WIDTH){1'b0} } , { (`DATA_WIDTH){1'b1} } } );
					ref_oflow = ( packet_3.opb == 0 ) ? 1 : 0;
				end
				else ref_err = 1;
			end

			8:begin // COMPARISON 
				if( packet_3.inp_valid == 3 )
				begin

					ref_res = 16'bz;

					if (packet_3.opa == packet_3.opb )
					begin
						ref_e = 'b1;
						ref_g = 'bz;
						ref_l = 'bz;
					end

					else if( packet_3.opa > packet_3.opb )
					begin
						ref_e = 'bz;
						ref_g = 'b1;
						ref_l = 'bz;
					end		          

					else 
					begin
						ref_e = 'bz;
						ref_g = 'bz;
						ref_l = 'b1;
					end

				end
				else ref_err = 1;
			end

			9:begin // INCREMENT AND MULTIPLY
				if(packet_3.inp_valid == 3) begin
					t_mul  = ( packet_3.opa + 1 ) * ( packet_3.opb + 1 );  
					ref_res =  t_mul;
				end
				else ref_err = 1;
			end

			10:begin // SHIFT AND MULTIPLY
				if(packet_3.inp_valid == 3) begin
					bit [`DATA_WIDTH - 1:0] temp = ( packet_3.opa << 1 ); 
					t_mul  = ( temp ) * ( packet_3.opb );
					ref_res =  t_mul;
				end
				else ref_err = 1;
			end
			default:begin
				ref_err = 1;
			end
		endcase    
	endtask

	//------------------------------------------------------//
	//           performs the logical operation             //
	//------------------------------------------------------//

	task logical_operation(input alu_sequence_item packet_3);
		case(packet_3.cmd)

			0: begin // BITWISE AND
				if(packet_3.inp_valid == 3) begin
					ref_res = ( packet_3.opa & packet_3.opb ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } ); 
				end
				else ref_err = 1;
			end

			1: begin // BITWISE NAND
				if(packet_3.inp_valid == 3) begin
					ref_res = ( ~( packet_3.opa & packet_3.opb ) ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } ); 
				end
				else ref_err = 1;
			end

			2: begin // BITWISE OR
				if(packet_3.inp_valid == 3) begin
					ref_res = ( packet_3.opa | packet_3.opb ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } ); 
				end
				else ref_err = 1;
			end

			3: begin // BITWISE NOR
				if(packet_3.inp_valid == 3) begin
					ref_res = ( ~( packet_3.opa | packet_3.opb ) ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } ); 
				end
				else ref_err = 1;
			end

			4: begin // BITWISE XOR
				if(packet_3.inp_valid == 3) begin
					ref_res = ( packet_3.opa ^ packet_3.opb ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } ); 
				end
				else ref_err = 1;
			end

			5: begin // BITWISE XNOR
				if(packet_3.inp_valid == 3) begin
					ref_res = ( ~( packet_3.opa ^ packet_3.opb ) ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } ); 
				end
				else ref_err = 1;
			end

			6: begin // NOT A
				if(packet_3.inp_valid == 1) begin
					ref_res = ( ~( packet_3.opa ) ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } );
				end
				else ref_err = 1;
			end

			7: begin // NOT B
				if(packet_3.inp_valid == 2) begin
					ref_res = ( ~( packet_3.opb ) ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } );
				end
				else ref_err = 1;
			end

			8: begin // SHIFT RIGHT A
				if(packet_3.inp_valid == 1) begin
					ref_res = ( ( packet_3.opa ) >> 1 ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } );
				end
				else ref_err = 1;
			end

			9: begin // SHIFT LEFT A
				if(packet_3.inp_valid == 1) begin
					ref_res = ( ( packet_3.opa ) << 1 ) & ( { {`DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } );
				end
				else ref_err = 1;
			end

			10: begin // SHIFT RIGHT B
				if(packet_3.inp_valid == 2) begin
					ref_res = ( ( packet_3.opb ) >> 1 ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } );
				end
				else ref_err = 1;
			end

			11: begin // SHIFT LEFT B
				if(packet_3.inp_valid == 2) begin
					ref_res = ( ( packet_3.opb ) << 1 ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } );
				end
				else ref_err = 1;
			end

			12: begin // ROTATE LEFT 
				if(packet_3.inp_valid == 3) begin
					ref_res[ `DATA_WIDTH : 0 ] = 
						( ( packet_3.opa << packet_3.opb[($clog2(`DATA_WIDTH) - 1):0] ) | ( packet_3.opa >> ( `DATA_WIDTH - packet_3.opb[($clog2(`DATA_WIDTH) - 1):0]) ) ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } );

					if(|(packet_3.opb[ `DATA_WIDTH - 1 : ($clog2(`DATA_WIDTH) + 1)]))      
						ref_err = 1; 
					else          
						ref_err = 0;
				end
				else ref_err = 1;
			end

			13: begin // ROTATE RIGHT
				if(packet_3.inp_valid == 3) begin
					ref_res[ `DATA_WIDTH : 0 ] = 
						( ( packet_3.opa >> packet_3.opb[($clog2(`DATA_WIDTH) - 1):0] ) | ( packet_3.opa << ( `DATA_WIDTH - packet_3.opb[($clog2(`DATA_WIDTH) - 1):0]) ) ) & ( { { `DATA_WIDTH{1'b0} } , { `DATA_WIDTH{1'b1} } } );

					if(|(packet_3.opb[ `DATA_WIDTH - 1 : ($clog2(`DATA_WIDTH) + 1)]))      
						ref_err = 1; 
					else          
						ref_err = 0;
				end
				else ref_err = 1;
			end

			default : begin
				ref_err = 1;
			end
		endcase
	endtask

	//------------------------------------------------------//
	// performs the comparsion report by checking bit by    //
	// bit between the reference result and monitor results //   
	//------------------------------------------------------//

	task comparision_report();
		if( monitor_results === reference_results )
			$display("<-----------------------------PASS----------------------------->" );
		else
			$display("<-----------------------------FAIL----------------------------->" );
	endtask
endclass
