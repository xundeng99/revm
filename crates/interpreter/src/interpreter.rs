pub mod analysis;
mod contract;
#[cfg(feature = "serde")]
pub mod serde;
mod shared_memory;
mod stack;

pub use contract::Contract;
pub use shared_memory::{num_words, SharedMemory, EMPTY_SHARED_MEMORY};
pub use stack::{Stack, STACK_LIMIT};

use crate::EOFCreateOutcome;
use crate::{
    gas, primitives::Bytes, push, push_b256, return_ok, return_revert, CallOutcome, CreateOutcome,
    FunctionStack, Gas, Host, InstructionResult, InterpreterAction,
};
use core::cmp::min;
use core::hash::Hash;
use revm_primitives::{Bytecode, Eof, U256};
use std::borrow::ToOwned;
use std::collections::HashMap;


/// EVM bytecode interpreter.
#[derive(Debug)]
pub struct Interpreter {
    /// The current instruction pointer.
    pub instruction_pointer: *const u8,
    /// The gas state.
    pub gas: Gas,
    /// Contract information and invoking data
    pub contract: Contract,
    /// The execution control flag. If this is not set to `Continue`, the interpreter will stop
    /// execution.
    pub instruction_result: InstructionResult,
    /// Currently run Bytecode that instruction result will point to.
    /// Bytecode is owned by the contract.
    pub bytecode: Bytes,
    /// Whether we are Interpreting the Ethereum Object Format (EOF) bytecode.
    /// This is local field that is set from `contract.is_eof()`.
    pub is_eof: bool,
    /// Is init flag for eof create
    pub is_eof_init: bool,
    /// Shared memory.
    ///
    /// Note: This field is only set while running the interpreter loop.
    /// Otherwise it is taken and replaced with empty shared memory.
    pub shared_memory: SharedMemory,
    /// Stack.
    pub stack: Stack,
    /// EOF function stack.
    pub function_stack: FunctionStack,
    /// The return data buffer for internal calls.
    /// It has multi usage:
    ///
    /// * It contains the output bytes of call sub call.
    /// * When this interpreter finishes execution it contains the output bytes of this contract.
    pub return_data_buffer: Bytes,
    /// Whether the interpreter is in "staticcall" mode, meaning no state changes can happen.
    pub is_static: bool,
    /// Actions that the EVM should do.
    ///
    /// Set inside CALL or CREATE instructions and RETURN or REVERT instructions. Additionally those instructions will set
    /// InstructionResult to CallOrCreate/Return/Revert so we know the reason.
    pub next_action: InterpreterAction,
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new(Contract::default(), 0, false)
    }
}

/// The result of an interpreter operation.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(::serde::Serialize, ::serde::Deserialize))]
pub struct InterpreterResult {
    /// The result of the instruction execution.
    pub result: InstructionResult,
    /// The output of the instruction execution.
    pub output: Bytes,
    /// The gas usage information.
    pub gas: Gas,
}


/*  Solidity Error Code
enum class PanicCode
{
	Generic = 0x00, // generic / unspecified error
	Assert = 0x01, // used by the assert() builtin
	UnderOverflow = 0x11, // arithmetic underflow or overflow
	DivisionByZero = 0x12, // division or modulo by zero
	EnumConversionError = 0x21, // enum conversion error
	StorageEncodingError = 0x22, // invalid encoding in storage
	EmptyArrayPop = 0x31, // empty array pop
	ArrayOutOfBounds = 0x32, // array out of bounds access
	ResourceError = 0x41, // resource error (too large allocation or too large array)
	InvalidInternalFunction = 0x51, // calling invalid internal function
};

*/
fn func_select_table(bytes: &[u8], map : &mut HashMap<usize, HashMap<U256, usize>>){
    let mut i = 0;
    while i < bytes.len() {
        let op = *bytes.get(i).unwrap();
        if (0x60..=0x7f).contains(&op) {
            i += 1; 
            i += op as usize - 0x5f;
        }
        else if op == 0x80 {
            match  bytes[i..=i+10] {
                [0x80, 0x63, v1, v2, v3, v4, 0x14, 0x61, d1, d2, 0x57] =>{
                    let idx = i;
                    let val:U256 = U256::from_be_bytes([ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
                        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
                        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
                        0x00, 0x00, 0x00, 0x00, v1, v2, v3, v4]);
                    let dst:usize = usize::from_be_bytes([0, 0, 0, 0, 0, 0, d1,d2]);
                    let mut innermap = HashMap::new();
                    innermap.insert(val, dst);
                    i += 11;
                    while (match bytes[i..=i+10] {
                        [0x80, 0x63, v1, v2, v3, v4, 0x14, 0x61, d1, d2, 0x57] =>{
                            let val1:U256 = U256::from_be_bytes([ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
                                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
                                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
                                0x00, 0x00, 0x00, 0x00, v1, v2, v3, v4]);
                            let dst1:usize = usize::from_be_bytes([0, 0, 0, 0, 0, 0, d1,d2]);
                            innermap.insert(val1, dst1);
                            i += 11;
                            true
                        }
                        _ =>{false}                  
                    }){}
                    map.insert(idx, innermap);

                }
                _ =>{i += 1;}                  
            }
        }
        else{
            i += 1;
        }
    }
       
}

fn find_panic_code(data: &[u8], map : &mut HashMap<usize, usize>){
    // ------- work ---------------
    // 0x41 can be substituted by other error codes
    // Push1 0x41 Push1 0x4 MSTORE PUSH1 0x24 Push1 0x0 Revert
    // 604160045260246000fd
    // ------- work ---------------

    // JUMPDEST PUSH32 (error message)
    // Push1 0x0 
    // MSTORE 
    // Push1 0x41 
    // Push1 0x4 
    // MSTORE 
    // PUSH1 0x24 
    // Push1 0x0 
    // Revert
    // 600052604160045260246000fd

    let mut indices: Vec<usize> = Vec::new();

    let bypass_panic = vec![0x11, 0x12, 0x32, 0x41];

    for (index, byte) in data.iter().enumerate() {
        if *byte == 0xfd && index > 46 {
            match  data[(index-12)..=index] {
                [0x60, 0x00, 0x52, 0x60, panc, 0x60, 0x04, 0x52, 0x60, 0x24, 0x60, 0x00, 0xfd] => {
                    //println!("pattern found!{}", index + 1);
                    if bypass_panic.contains(&panc){
                        let mut found = false;  
                        let mut iter = index - 9;
                        while (!found && iter > 0) {
                            // JUMPDEST
                            if(data[iter] == 0x5b){
                                found = true;
                                //println!("At idx {} found {}!\n", iter, index);
                                map.insert(iter, index);
                            }
                            //JUMPI or JUMP
                            else if(data[iter] == 0x57 || data[iter] == 0x56){
                                //println!("quit early: {} {}", index, iter);
                                map.insert(iter + 1, index);
                                found = true;
                            }
                            else{
                                iter = iter - 1;
                            }
            
                        }                 
                        
                    }else{}
                },
                _ => {},
            } 
        }
    }
    
}


fn build_push_map(bytes: &[u8], map : &mut HashMap<usize, usize>){
    let mut i = 0;
    while i < bytes.len() {
        let op = *bytes.get(i).unwrap();
        i += 1;
        // skipping push

        if (0x60..=0x7f).contains(&op) {
            let num_bytes = op as usize - 0x5f;
            map.insert(i + num_bytes -1, num_bytes);
            i += op as usize - 0x5f;
        }
    }
}


// TODO: FIX 
fn find_pattern_indices(bytes: &[u8], map : &mut HashMap<usize, usize>){
    // -------This did not work ---------------
    // Pattern1   Pattern2 (working)
    // JUMPI/Other op       JUMPDEST
    // ...
    // Revert      Revert

    let mut i = 0;
    let mut jump_point = Default::default(); 
    // Not sure if need this
    // let last_op = *bytes.last().unwrap();
    // let has_cbor = last_op != 0x56 || last_op != 0x57 || last_op != 0 || last_op != 0xfe|| last_op != 0xfd || last_op != 0xf3;

    // let cbor_len = if has_cbor {
    //     // load last 2 bytes as big endian
    //     let len = bytes.len();
    //     let last_2 = *bytes.get(len - 2).unwrap() as usize;
    //     let last_1 = *bytes.get(len - 1).unwrap() as usize;
    //     (last_2 << 8) + last_1 + 2
    // } else {
    //     0
    // };
    // println!("{}, {}", bytes.len(), cbor_len);
    // if bytes.len() == 0{
    //     return
    // }
    while i < bytes.len() {
        let op = *bytes.get(i).unwrap();
        i += 1;
        // skipping push
        if (0x60..=0x7f).contains(&op) {
            i += op as usize - 0x5f;
        }
        else if op == 0x5b{
            jump_point = i - 1;
        }
        else if(op == 0x57 || op == 0x56 || op != 0 || op != 0xfe || op != 0xfd || op != 0xf3){
            jump_point = i;
        }
        else if op == 0xfd{
            //println!("At idx {} found fd!\n", index);
            map.insert(jump_point, i);
            }
        }
}

impl Interpreter {
    /// Create new interpreter
    pub fn new(contract: Contract, gas_limit: u64, is_static: bool) -> Self {
        if !contract.bytecode.is_execution_ready() {
            panic!("Contract is not execution ready {:?}", contract.bytecode);
        }
        let is_eof = contract.bytecode.is_eof();
        let bytecode = contract.bytecode.bytecode().clone();
        Self {
            instruction_pointer: bytecode.as_ptr(),
            bytecode,
            contract,
            gas: Gas::new(gas_limit),
            instruction_result: InstructionResult::Continue,
            function_stack: FunctionStack::default(),
            is_static,
            is_eof,
            is_eof_init: false,
            return_data_buffer: Bytes::new(),
            shared_memory: EMPTY_SHARED_MEMORY,
            stack: Stack::new(),
            next_action: InterpreterAction::None,
        }
    }

    /// Set set is_eof_init to true, this is used to enable `RETURNCONTRACT` opcode.
    #[inline]
    pub fn set_is_eof_init(&mut self) {
        self.is_eof_init = true;
    }

    #[inline]
    pub fn eof(&self) -> Option<&Eof> {
        self.contract.bytecode.eof()
    }

    /// Test related helper
    #[cfg(test)]
    pub fn new_bytecode(bytecode: Bytecode) -> Self {
        Self::new(
            Contract::new(
                Bytes::new(),
                bytecode,
                None,
                crate::primitives::Address::default(),
                crate::primitives::Address::default(),
                U256::ZERO,
            ),
            0,
            false,
        )
    }

    /// Load EOF code into interpreter. PC is assumed to be correctly set
    pub(crate) fn load_eof_code(&mut self, idx: usize, pc: usize) {
        // SAFETY: eof flag is true only if bytecode is Eof.
        let Bytecode::Eof(eof) = &self.contract.bytecode else {
            panic!("Expected EOF bytecode")
        };
        let Some(code) = eof.body.code(idx) else {
            panic!("Code not found")
        };
        self.bytecode = code.clone();
        self.instruction_pointer = unsafe { self.bytecode.as_ptr().add(pc) };
    }

    /// Inserts the output of a `create` call into the interpreter.
    ///
    /// This function is used after a `create` call has been executed. It processes the outcome
    /// of that call and updates the state of the interpreter accordingly.
    ///
    /// # Arguments
    ///
    /// * `create_outcome` - A `CreateOutcome` struct containing the results of the `create` call.
    ///
    /// # Behavior
    ///
    /// The function updates the `return_data_buffer` with the data from `create_outcome`.
    /// Depending on the `InstructionResult` indicated by `create_outcome`, it performs one of the following:
    ///
    /// - `Ok`: Pushes the address from `create_outcome` to the stack, updates gas costs, and records any gas refunds.
    /// - `Revert`: Pushes `U256::ZERO` to the stack and updates gas costs.
    /// - `FatalExternalError`: Sets the `instruction_result` to `InstructionResult::FatalExternalError`.
    /// - `Default`: Pushes `U256::ZERO` to the stack.
    ///
    /// # Side Effects
    ///
    /// - Updates `return_data_buffer` with the data from `create_outcome`.
    /// - Modifies the stack by pushing values depending on the `InstructionResult`.
    /// - Updates gas costs and records refunds in the interpreter's `gas` field.
    /// - May alter `instruction_result` in case of external errors.
    pub fn insert_create_outcome(&mut self, create_outcome: CreateOutcome) {
        self.instruction_result = InstructionResult::Continue;

        let instruction_result = create_outcome.instruction_result();
        self.return_data_buffer = if instruction_result.is_revert() {
            // Save data to return data buffer if the create reverted
            create_outcome.output().to_owned()
        } else {
            // Otherwise clear it
            Bytes::new()
        };

        match instruction_result {
            return_ok!() => {
                let address = create_outcome.address;
                push_b256!(self, address.unwrap_or_default().into_word());
                self.gas.erase_cost(create_outcome.gas().remaining());
                self.gas.record_refund(create_outcome.gas().refunded());
            }
            return_revert!() => {
                push!(self, U256::ZERO);
                self.gas.erase_cost(create_outcome.gas().remaining());
            }
            InstructionResult::FatalExternalError => {
                panic!("Fatal external error in insert_create_outcome");
            }
            _ => {
                push!(self, U256::ZERO);
            }
        }
    }

    pub fn insert_eofcreate_outcome(&mut self, create_outcome: EOFCreateOutcome) {
        let instruction_result = create_outcome.instruction_result();

        self.return_data_buffer = if *instruction_result == InstructionResult::Revert {
            // Save data to return data buffer if the create reverted
            create_outcome.output().to_owned()
        } else {
            // Otherwise clear it. Note that RETURN opcode should abort.
            Bytes::new()
        };

        match instruction_result {
            InstructionResult::ReturnContract => {
                push_b256!(self, create_outcome.address.into_word());
                self.gas.erase_cost(create_outcome.gas().remaining());
                self.gas.record_refund(create_outcome.gas().refunded());
            }
            return_revert!() => {
                push!(self, U256::ZERO);
                self.gas.erase_cost(create_outcome.gas().remaining());
            }
            InstructionResult::FatalExternalError => {
                panic!("Fatal external error in insert_eofcreate_outcome");
            }
            _ => {
                push!(self, U256::ZERO);
            }
        }
    }

    /// Inserts the outcome of a call into the virtual machine's state.
    ///
    /// This function takes the result of a call, represented by `CallOutcome`,
    /// and updates the virtual machine's state accordingly. It involves updating
    /// the return data buffer, handling gas accounting, and setting the memory
    /// in shared storage based on the outcome of the call.
    ///
    /// # Arguments
    ///
    /// * `shared_memory` - A mutable reference to the shared memory used by the virtual machine.
    /// * `call_outcome` - The outcome of the call to be processed, containing details such as
    ///   instruction result, gas information, and output data.
    ///
    /// # Behavior
    ///
    /// The function first copies the output data from the call outcome to the virtual machine's
    /// return data buffer. It then checks the instruction result from the call outcome:
    ///
    /// - `return_ok!()`: Processes successful execution, refunds gas, and updates shared memory.
    /// - `return_revert!()`: Handles a revert by only updating the gas usage and shared memory.
    /// - `InstructionResult::FatalExternalError`: Sets the instruction result to a fatal external error.
    /// - Any other result: No specific action is taken.
    pub fn insert_call_outcome(
        &mut self,
        shared_memory: &mut SharedMemory,
        call_outcome: CallOutcome,
    ) {
        self.instruction_result = InstructionResult::Continue;
        self.return_data_buffer.clone_from(call_outcome.output());

        let out_offset = call_outcome.memory_start();
        let out_len = call_outcome.memory_length();

        let target_len = min(out_len, self.return_data_buffer.len());
        match call_outcome.instruction_result() {
            return_ok!() => {
                // return unspend gas.
                let remaining = call_outcome.gas().remaining();
                let refunded = call_outcome.gas().refunded();
                self.gas.erase_cost(remaining);
                self.gas.record_refund(refunded);
                shared_memory.set(out_offset, &self.return_data_buffer[..target_len]);
                push!(self, U256::from(1));
            }
            return_revert!() => {
                self.gas.erase_cost(call_outcome.gas().remaining());
                shared_memory.set(out_offset, &self.return_data_buffer[..target_len]);
                push!(self, U256::ZERO);
            }
            InstructionResult::FatalExternalError => {
                panic!("Fatal external error in insert_call_outcome");
            }
            _ => {
                push!(self, U256::ZERO);
            }
        }
    }

    /// Returns the opcode at the current instruction pointer.
    #[inline]
    pub fn current_opcode(&self) -> u8 {
        unsafe { *self.instruction_pointer }
    }

    /// Returns a reference to the contract.
    #[inline]
    pub fn contract(&self) -> &Contract {
        &self.contract
    }

    /// Returns a reference to the interpreter's gas state.
    #[inline]
    pub fn gas(&self) -> &Gas {
        &self.gas
    }

    /// Returns a reference to the interpreter's stack.
    #[inline]
    pub fn stack(&self) -> &Stack {
        &self.stack
    }

    /// Returns the current program counter.
    #[inline]
    pub fn program_counter(&self) -> usize {
        // SAFETY: `instruction_pointer` should be at an offset from the start of the bytecode.
        // In practice this is always true unless a caller modifies the `instruction_pointer` field manually.
        unsafe { self.instruction_pointer.offset_from(self.bytecode.as_ptr()) as usize }
    }

    /// Executes the instruction at the current instruction pointer.
    ///
    /// Internally it will increment instruction pointer by one.
    #[inline]
    pub(crate) fn step<FN, H: Host + ?Sized>(&mut self, instruction_table: &[FN; 256], host: &mut H)
    where
        FN: Fn(&mut Interpreter, &mut H),
    {
        // Get current opcode.
        let opcode = unsafe { *self.instruction_pointer };

        // SAFETY: In analysis we are doing padding of bytecode so that we are sure that last
        // byte instruction is STOP so we are safe to just increment program_counter bcs on last instruction
        // it will do noop and just stop execution of this contract
        self.instruction_pointer = unsafe { self.instruction_pointer.offset(1) };

        // execute instruction.
        (instruction_table[opcode as usize])(self, host)
    }

    #[inline]
    pub(crate) fn step_skip<FN, H: Host + ?Sized>(&mut self, instruction_table: &[FN; 256], host: &mut H, skip_map: &HashMap<usize, usize>, fs_map: &HashMap<usize, HashMap<U256, usize>>)
    where
        FN: Fn(&mut Interpreter, &mut H),
    {
        let pc = &self.program_counter();
        if skip_map.contains_key(pc){
            let value = skip_map.get(&self.program_counter());
            println!("Revert Ahead at pc{}, {}!", self.program_counter(), unsafe {*self.instruction_pointer});
            (instruction_table[0xfd as usize])(self, host)
        }else if (fs_map.contains_key(pc)){
            // println!("Jump Ahead");
            let innermap = fs_map.get(pc).unwrap();
            let val:U256 = self.stack.peek(0).unwrap();
            if innermap.contains_key(&val){
                let dst = innermap.get(&val).unwrap();
                self.instruction_pointer = unsafe { self.bytecode.as_ptr().add(*dst) };
            }
            // TODO: FIX Default branch 
            else{
                // Get current opcode.
                let opcode = unsafe { *self.instruction_pointer };

                // SAFETY: In analysis we are doing padding of bytecode so that we are sure that last
                // byte instruction is STOP so we are safe to just increment program_counter bcs on last instruction
                // it will do noop and just stop execution of this contract
                self.instruction_pointer = unsafe { self.instruction_pointer.offset(1) };

                // execute instruction.
                (instruction_table[opcode as usize])(self, host)
            }
        }           
        else{
            // Get current opcode.
            let opcode = unsafe { *self.instruction_pointer };

            // SAFETY: In analysis we are doing padding of bytecode so that we are sure that last
            // byte instruction is STOP so we are safe to just increment program_counter bcs on last instruction
            // it will do noop and just stop execution of this contract
            self.instruction_pointer = unsafe { self.instruction_pointer.offset(1) };

            // execute instruction.
            (instruction_table[opcode as usize])(self, host)
        }
    }

    /// Take memory and replace it with empty memory.
    pub fn take_memory(&mut self) -> SharedMemory {
        core::mem::replace(&mut self.shared_memory, EMPTY_SHARED_MEMORY)
    }

    /// Executes the interpreter until it returns or stops.
    pub fn run<FN, H: Host + ?Sized>(
        &mut self,
        shared_memory: SharedMemory,
        instruction_table: &[FN; 256],
        host: &mut H,
    ) -> InterpreterAction
    where
        FN: Fn(&mut Interpreter, &mut H),
    {
        self.next_action = InterpreterAction::None;
        self.shared_memory = shared_memory;

        // Find bbs with revert as last instruction
        let bytecode_analysis = self.contract.bytecode.original_byte_slice().clone();
        let mut skip_map: HashMap<usize, usize> = HashMap::new();
        let mut push_map: HashMap<usize, usize> = HashMap::new();
        let mut func_selector_map: HashMap<usize, HashMap<U256, usize>> = HashMap::new();
        
        //find_panic_code(bytecode_analysis, &mut skip_map);

        //build_push_map(&bytecode_analysis, &mut push_map);
        //find_pattern_indices(&bytecode_analysis, &mut skip_map);
        func_select_table(&bytecode_analysis, &mut func_selector_map);


        // println!{"first bytecode"}
        // for el in bytecode_analysis {
        //      println!("{:02x}", el);
        // }

        // for (key, value) in &func_selector_map {
        //     for (k1, v1) in value{
        //         println!("{} : ({:06x}: {:06x})", key, k1, v1);

        //     }
            
        // }
        // main loop
        while self.instruction_result == InstructionResult::Continue {
            //self.step(instruction_table, host)
            self.step_skip(instruction_table, host, &skip_map, &func_selector_map);
        }

        // Return next action if it is some.
        if self.next_action.is_some() {
            return core::mem::take(&mut self.next_action);
        }
        // If not, return action without output as it is a halt.
        InterpreterAction::Return {
            result: InterpreterResult {
                result: self.instruction_result,
                // return empty bytecode
                output: Bytes::new(),
                gas: self.gas,
            },
        }
    }

    /// Resize the memory to the new size. Returns whether the gas was enough to resize the memory.
    #[inline]
    #[must_use]
    pub fn resize_memory(&mut self, new_size: usize) -> bool {
        resize_memory(&mut self.shared_memory, &mut self.gas, new_size)
    }
}

impl InterpreterResult {
    /// Returns whether the instruction result is a success.
    #[inline]
    pub const fn is_ok(&self) -> bool {
        self.result.is_ok()
    }

    /// Returns whether the instruction result is a revert.
    #[inline]
    pub const fn is_revert(&self) -> bool {
        self.result.is_revert()
    }

    /// Returns whether the instruction result is an error.
    #[inline]
    pub const fn is_error(&self) -> bool {
        self.result.is_error()
    }
}


/// Resize the memory to the new size. Returns whether the gas was enough to resize the memory.
#[inline(never)]
#[cold]
#[must_use]
pub fn resize_memory(memory: &mut SharedMemory, gas: &mut Gas, new_size: usize) -> bool {
    let new_words = num_words(new_size as u64);
    let new_cost = gas::memory_gas(new_words);
    let current_cost = memory.current_expansion_cost();
    let cost = new_cost - current_cost;
    let success = gas.record_cost(cost);
    if success {
        memory.resize((new_words as usize) * 32);
    }
    success
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{opcode::InstructionTable, DummyHost};
    use revm_primitives::CancunSpec;

    #[test]
    fn object_safety() {
        let mut interp = Interpreter::new(Contract::default(), u64::MAX, false);

        let mut host = crate::DummyHost::default();
        let table: InstructionTable<DummyHost> =
            crate::opcode::make_instruction_table::<DummyHost, CancunSpec>();
        let _ = interp.run(EMPTY_SHARED_MEMORY, &table, &mut host);

        let host: &mut dyn Host = &mut host as &mut dyn Host;
        let table: InstructionTable<dyn Host> =
            crate::opcode::make_instruction_table::<dyn Host, CancunSpec>();
        let _ = interp.run(EMPTY_SHARED_MEMORY, &table, host);
    }
}
