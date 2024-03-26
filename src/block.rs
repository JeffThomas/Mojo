use std::sync::Arc;
use crate::instruction::Instruction;
use crate::signature::Signature;

pub struct Block {
    pub signature: Signature,
    pub code: Arc<dyn Instruction>
}


impl Block {

}