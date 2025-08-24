# ALU_VERIFICATION TESTBENCH ARCHITECTURE(UVM)
<img width="1024" height="720" alt="image" src="https://github.com/user-attachments/assets/b4cd8357-cf65-41e2-98ae-d1fcf579a9f7" />

# ALU Verification Project (UVM)

## 📌 Project Overview
An **Arithmetic Logic Unit (ALU)** is a digital circuit that performs arithmetic and logical operations.  
It is a fundamental building block of a CPU.
The performance and efficiency of the ALU directly impact the overall speed and capability of a computer system.  

This project focuses on verifying the ALU design using **SystemVerilog** and the **UVM methodology**.  
## The main objectives are:
•	To construct a verification planar that includes test plan, functional coverage plan and assertion plan.

•	To Design and built a ALU Testbench architecture (UVM) along with a structured code plan for testbench components.

•	To implement functional coverage and assertions in the ALU testbench and validate the ALU’s functional correctness along with its timings and find its design flaws. 

---

## ⚡ DUT Specification

### ALU Signals
| **Signal**       | **Direction** | **Width/Size** | **Description** |
|------------------|---------------|----------------|-----------------|
| Clock            | Input  | 1 | Positive edge-triggering signal |
| Reset            | Input  | 1 | Active-high synchronous reset (resets outputs to 0) |
| Clock Enable     | Input  | 1 | Active-high signal to enable ALU operations |
| Mode             | Input  | 1 | `1 → Arithmetic` <br> `0 → Logical` |
| Command          | Input  | Param (4-bit default) | Selects arithmetic/logical operation (see below) |
| Input Valid      | Input  | 2 | Operand select <br> `00`: None <br> `01`: A <br> `10`: B <br> `11`: A & B |
| Operand A        | Input  | Parameterized | Operand A input |
| Operand B        | Input  | Parameterized | Operand B input |
| Carry in         | Input  | 1 | 1-bit carry input |
| Result           | Output | Parameterized | Computed ALU result |
| Overflow         | Output | 1 | Indicates arithmetic overflow |
| Carry out        | Output | 1 | Indicates carry generation |
| Equal            | Output | 1 | A == B |
| Greater          | Output | 1 | A > B |
| Lesser           | Output | 1 | A < B |
| Error            | Output | 1 | Indicates invalid input or unsupported operation |

### Arithmetic Commands
| CMD | Operation |
|-----|-----------|
| 0   | ADD |
| 1   | SUB |
| 2   | ADD with Carry |
| 3   | SUB with Carry |
| 4   | INC_A |
| 5   | DEC_A |
| 6   | INC_B |
| 7   | DEC_B |
| 8   | COMPARE |
| 9   | INCREMENT AND MULTIPLY |
| 10  | SHIFT AND MULTIPLY|

### Logical Commands
| CMD | Operation |
|-----|-----------|
| 0   | AND |
| 1   | NAND |
| 2   | OR |
| 3   | NOR |
| 4   | XOR |
| 5   | XNOR |
| 6   | NOT A |
| 7   | NOT B |
| 8   | SHR1_A |
| 9   | SHL1_A |
| 10  | SHR1_B |
| 11  | SHL1_B |
| 12  | ROL_A_B |
| 13  | ROR_A_B |

---

## 🏗️ Testbench Architecture (UVM)

The UVM Testbench consists of the following components:

- **Sequence Item** → Defines transaction data.
- **Sequence** → Generates stimulus and sends to sequencer.
- **Sequencer** → Controls flow of transactions to driver.
- **Driver** → Drives DUT signals based on sequence items.
- **Monitor**
  - **Active Monitor** → Captures DUT inputs.
  - **Passive Monitor** → Captures DUT outputs.
- **Agent**
  - **Active Agent** → Contains sequencer, driver, and input monitor.
  - **Passive Agent** → Contains only output monitor.
- **Scoreboard** → Compares DUT outputs with reference model.
- **Coverage (Subscriber)** → Collects functional coverage (input/output covergroups).
- **Environment (env)** → Integrates agent, scoreboard, and coverage.
- **Test** → Top-level UVM component that configures and runs sequences.
- **Top Module** → Instantiates DUT, connects interface, and runs UVM test.
- **Interface** → Bundles DUT signals, defines clocking blocks and modports.
- **DUV** → The ALU design under verification.

---

# 🧪 Verification Results

## 🔴 Design Flaws Detected
###  During Normal Operation (without 16 clock cycle): 
1)	DUT Result width is not matching with the testbench result width.

2)	Input Valid Selection flaws:
When input valid is 0, it will not produce the expected error result during single operand operation as well as two operand operation.

3)  DUT Functionality flaws:
   
| **Mode**     | **Command**           | **Failure Reason** |
|--------------|-----------------------|---------------------|
| Arithmetic   | Sub                   | Overflow condition failed when both operands are equal |
| Arithmetic   | Sub Cin               | Overflow condition failed when both operands are equal |
| Arithmetic   | INC_A                 | Increment A functionality failed |
| Arithmetic   | INC_A                 | Failed to produce carry-out result on INC_A |
| Arithmetic   | DEC_A                 | Failed to produce Overflow result on DEC_A |
| Arithmetic   | INC_B                 | Increment B functionality failed |
| Arithmetic   | INC_B                 | Failed to produce carry-out result on INC_B |
| Arithmetic   | DEC_B                 | Decrement B functionality failed |
| Arithmetic   | DEC_B                 | Failed to produce Overflow result on DEC_B |
| Arithmetic   | Shift and multiply    | Shift and multiply functionality failed |
| Logical      | Logical OR            | Failed to perform logical OR operation |
| Logical      | Shift Right A         | Shift right on A operation failed |
| Logical      | Shift Right B         | Shift right on B operation failed |
| Logical      | Rotate right A on B   | Error bit from [7:4] on Operand B failed |

### During 16 cycle Operation (with 16 clock cycle):
1)	Whenever the 16-cycle operation is implemented on both arithmetic and logical operation it will not produce error result when input valid is 0 or 1 or 2. It will only pass when input valid is 3.
   
2)	Whenever the count is greater than or equal to 16 and input valid is either 0, 1, or 2. It will not produce error result. It will pass when input valid is 3.

### 📊 Coverage Report
- Input Coverage ✅
  
  <img width="1024" height="720" alt="image" src="https://github.com/user-attachments/assets/5ca83af7-4c7e-438b-930d-a0fe0768e0d6" />

- Output Coverage ✅
  
  <img width="1024" height="720" alt="image" src="https://github.com/user-attachments/assets/18c053c7-811f-4af9-b1b0-88ffd8457c4b" />

- Assertion Coverage ✅

  <img width="1024" height="720" alt="image" src="https://github.com/user-attachments/assets/4e004b17-952b-4f17-8527-f20c81ea0795" />

- Overall Coverage ✅

  <img width="1024" height="720" alt="image" src="https://github.com/user-attachments/assets/02e9277f-c882-4a1b-81df-3c7533839344" />

---

## 📂 Resources
- **Test Plan:** [TEST PLAN LINK](https://docs.google.com/spreadsheets/d/1EryK2q-1XDE19L9bzLosvEQQzwqS2ouB/edit?usp=sharing)  
- **Functional Coverage Plan:** [COVERAGE LINK](https://docs.google.com/spreadsheets/d/1EryK2q-1XDE19L9bzLosvEQQzwqS2ouB/edit?usp=sharing)  
- **Assertions:** [ASSERTION LINK](https://docs.google.com/spreadsheets/d/1EryK2q-1XDE19L9bzLosvEQQzwqS2ouB/edit?usp=sharing)  

---

## 👨‍💻 Author
**Jason Linus Rodrigues**  

