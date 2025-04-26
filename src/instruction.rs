use std::fmt::Debug;
use std::sync::Arc;

use crate::MojoError;
use crate::value::Value;
use crate::value::Value::{Float, Int};

///The [ExecutionContext](ExecutionContext) stores state information for
/// an executing script. In our instance we just store aa stack of integers, a more complex
/// scripting language would use this object to store call stacks, namespaces, heaps etc. etc.
pub struct ExecutionContext {
  pub stack: Vec<Value>,
}

pub trait Instruction: Debug {
  fn execute(
    &self,
    ctx: &mut ExecutionContext,
  ) -> Result<Option<Arc<dyn Instruction>>, MojoError>;
}

impl PartialEq for dyn Instruction {
  fn eq(&self, _other: &Self) -> bool {
    return false;
  }

  fn ne(&self, _other: &Self) -> bool {
    return false;
  }
}

impl PartialEq<&Self> for dyn Instruction {
  fn eq(&self, _other: &&Self) -> bool {
    return false;
  }

  fn ne(&self, _other: &&Self) -> bool {
    return false;
  }
}

// A wrapper allowing us to put an Instruction in a Value.
//
// this wrapper is necessary because implementing PartialEq for a type of Arc
// is not allowed. This does not compile
// impl PartialEq for Arc<dyn Instruction> {
//
// But you can do it for a box, this compiles
// impl PartialEq for Box<dyn Instruction> {
//
// But you can't do it for an Arc and the standard PartialEq macro expansion causes
// "error[E0507]: cannot move out of `*__arg1_0` which is behind a shared reference"
#[derive(Debug, Clone)]
pub struct StupidInstructionBucket {
  pub i: Arc<dyn Instruction>,
}

impl PartialEq for StupidInstructionBucket {
  // Instructions are never equal to anything, why would you need to do this?
  fn eq(&self, _other: &Self) -> bool { return false; }
  fn ne(&self, _other: &Self) -> bool { return false; }
}

#[derive(Debug)]
pub struct IntInstruction {
  pub value: i32,
  pub next: Option<Arc<dyn Instruction>>,

  pub line: usize,
  pub column: usize,
}

impl Instruction for IntInstruction {
  // `execute` is the only function an Instruction has
  fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<Arc<dyn Instruction>>, MojoError> {
    // the insert happens here
    ctx.stack.push(Int(self.value));
    // return the next Instruction
    Ok(self.next.clone())
  }
}


#[derive(Debug)]
pub struct FloatInstruction {
  pub value: f32,
  pub next: Option<Arc<dyn Instruction>>,

  pub line: usize,
  pub column: usize,
}

impl Instruction for FloatInstruction {
  fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<Arc<dyn Instruction>>, MojoError> {
    ctx.stack.push(Float(self.value));
    Ok(self.next.clone())
  }
}


#[derive(Debug)]
pub struct AddInstruction {
  pub next: Option<Arc<dyn Instruction>>,

  pub line: usize,
  pub column: usize,
}

impl Instruction for AddInstruction {
  fn execute(
    &self,
    ctx: &mut ExecutionContext,
  ) -> Result<Option<Arc<dyn Instruction>>, MojoError> {
    let right = ctx.stack.pop().unwrap();
    let left = ctx.stack.pop().unwrap();
    match left {
      Int(li) => {
        match right {
          Int(ri) => {
            ctx.stack.push(Int(li + ri))
          }
          Float(rf) => {
            ctx.stack.push(Float(li as f32 + rf))
          }
          _ => {
            return Err(MojoError::Error(format!("Unknown right element at {}, {}", self.line, self.column).parse().unwrap()));
          }
        }
      }
      Float(lf) => {
        match right {
          Int(ri) => {
            ctx.stack.push(Float(lf + ri as f32))
          }
          Float(rf) => {
            ctx.stack.push(Float(lf + rf))
          }
          _ => {
            return Err(MojoError::Error(format!("Unknown right element at {}, {}", self.line, self.column).parse().unwrap()));
          }
        }
      }
      _ => {
        return Err(MojoError::Error(format!("Unknown left element at {}, {}", self.line, self.column).parse().unwrap()));
      }
    }
    Ok(self.next.clone())
  }
}

#[derive(Debug)]
pub struct SubtractInstruction {
  pub next: Option<Arc<dyn Instruction>>,

  pub line: usize,
  pub column: usize,
}

impl Instruction for SubtractInstruction {
  fn execute(
    &self,
    ctx: &mut ExecutionContext,
  ) -> Result<Option<Arc<dyn Instruction>>, MojoError> {
    let right = ctx.stack.pop().unwrap();
    let left = ctx.stack.pop().unwrap();
    match left {
      Int(li) => {
        match right {
          Int(ri) => {
            ctx.stack.push(Int(li - ri))
          }
          Float(rf) => {
            ctx.stack.push(Float(li as f32 - rf))
          }
          _ => {
            return Err(MojoError::Error(format!("Unknown right element at {}, {}", self.line, self.column).parse().unwrap()));
          }
        }
      }
      Float(lf) => {
        match right {
          Int(ri) => {
            ctx.stack.push(Float(lf - ri as f32))
          }
          Float(rf) => {
            ctx.stack.push(Float(lf - rf))
          }
          _ => {
            return Err(MojoError::Error(format!("Unknown right element at {}, {}", self.line, self.column).parse().unwrap()));
          }
        }
      }
      _ => {
        return Err(MojoError::Error(format!("Unknown left element at {}, {}", self.line, self.column).parse().unwrap()));
      }
    }
    Ok(self.next.clone())
  }
}

#[derive(Debug)]
pub struct MultiplyInstruction {
  pub next: Option<Arc<dyn Instruction>>,

  pub line: usize,
  pub column: usize,
}

impl Instruction for MultiplyInstruction {
  fn execute(
    &self,
    ctx: &mut ExecutionContext,
  ) -> Result<Option<Arc<dyn Instruction>>, MojoError> {
    let right = ctx.stack.pop().unwrap();
    let left = ctx.stack.pop().unwrap();
    match left {
      Int(li) => {
        match right {
          Int(ri) => {
            ctx.stack.push(Int(li * ri))
          }
          Float(rf) => {
            ctx.stack.push(Float(li as f32 * rf))
          }
          _ => {
            return Err(MojoError::Error(format!("Unknown right element at {}, {}", self.line, self.column).parse().unwrap()));
          }
        }
      }
      Float(lf) => {
        match right {
          Int(ri) => {
            ctx.stack.push(Float(lf * ri as f32))
          }
          Float(rf) => {
            ctx.stack.push(Float(lf * rf))
          }
          _ => {
            return Err(MojoError::Error(format!("Unknown right element at {}, {}", self.line, self.column).parse().unwrap()));
          }
        }
      }
      _ => {
        return Err(MojoError::Error(format!("Unknown left element at {}, {}", self.line, self.column).parse().unwrap()));
      }
    }
    Ok(self.next.clone())
  }
}

#[derive(Debug)]
pub struct DivideInstruction {
  pub next: Option<Arc<dyn Instruction>>,

  pub line: usize,
  pub column: usize,
}

impl Instruction for DivideInstruction {
  fn execute(
    &self,
    ctx: &mut ExecutionContext,
  ) -> Result<Option<Arc<dyn Instruction>>, MojoError> {
    let right = ctx.stack.pop().unwrap();
    let left = ctx.stack.pop().unwrap();
    match left {
      Int(li) => {
        match right {
          Int(ri) => {
            ctx.stack.push(Int(li / ri))
          }
          Float(rf) => {
            ctx.stack.push(Float(li as f32 / rf))
          }
          _ => {
            return Err(MojoError::Error(format!("Unknown right element at {}, {}", self.line, self.column).parse().unwrap()));
          }
        }
      }
      Float(lf) => {
        match right {
          Int(ri) => {
            ctx.stack.push(Float(lf / ri as f32))
          }
          Float(rf) => {
            ctx.stack.push(Float(lf / rf))
          }
          _ => {
            return Err(MojoError::Error(format!("Unknown right element at {}, {}", self.line, self.column).parse().unwrap()));
          }
        }
      }
      _ => {
        return Err(MojoError::Error(format!("Unknown left element at {}, {}", self.line, self.column).parse().unwrap()));
      }
    }
    Ok(self.next.clone())
  }
}

#[derive(Debug)]
pub struct NegateInstruction {
  pub next: Option<Arc<dyn Instruction>>,

  pub line: usize,
  pub column: usize,
}

impl Instruction for NegateInstruction {
  fn execute(
    &self,
    ctx: &mut ExecutionContext,
  ) -> Result<Option<Arc<dyn Instruction>>, MojoError> {
    let right = ctx.stack.pop().unwrap();
    match right {
      Int(i) => {
        ctx.stack.push(Int(-i))
      }
      Float(f) => {
        ctx.stack.push(Float(-f))
      }
      _ => {
        return Err(MojoError::Error(format!("Unknown right element at {}, {}", self.line, self.column).parse().unwrap()));
      }
    }
    Ok(self.next.clone())
  }
}

#[derive(Debug)]
pub struct TernaryInstruction {
  pub instruction: char,
  pub then_branch: Option<Arc<dyn Instruction>>,
  pub else_branch: Option<Arc<dyn Instruction>>,

  pub line: usize,
  pub column: usize,
}

impl Instruction for TernaryInstruction {
  fn execute(&self, ctx: &mut ExecutionContext) -> Result<Option<Arc<dyn Instruction>>, MojoError> {
    let if_results = ctx.stack.pop().unwrap();
    match if_results {
      Int(i) => {
        if i == 0 {
          return Ok(self.else_branch.clone());
        }
      }
      Float(f) => {
        if f == 0.0 {
          return Ok(self.else_branch.clone());
        }
      }
      _ => {
        return Err(MojoError::Error(format!("Unknown conditional element at {}, {}", self.line, self.column).parse().unwrap()));
      }
    }
    Ok(self.then_branch.clone())
  }
}