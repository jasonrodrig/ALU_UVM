interface alu_interface(input bit clk);

	// ALU input signals
	logic ce, mode , cin , rst;
	logic [`DATA_WIDTH - 1 :0] opa , opb; 
	logic [`CMD_WIDTH - 1 :0] cmd;
	logic [1:0] inp_valid;

	// ALU output signals
	logic [RESULT_WIDTH - 1 :0] res ;
	logic  err , oflow , cout , g , l , e;

	// Clocking block alu_driver_cb synchronizes DUT inputs
	clocking alu_driver_cb @(posedge clk);
		default input #1 output #1;
		output rst;
		output ce , mode ,cin;
		output cmd;
		output inp_valid;
		output opa , opb;  
	endclocking

	// Clocking block alu_monitor_cb synchronizes DUT inputs and outputs
	clocking alu_monitor_cb @(posedge clk);
		default input #1 output #1;
		input ce , mode ,cin ,rst;
		input cmd;
		input inp_valid;
		input opa , opb;  
		input res ;
		input err , oflow , cout , g , l , e;
	endclocking

	// Modport driver and monitor decleration
	modport DRIVER(clocking alu_driver_cb);
	modport MONITOR(clocking alu_monitor_cb);

endinterface
