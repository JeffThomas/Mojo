use std::cell::RefCell;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;

use lexx::token::Token;

use crate::instruction::{AddInstruction, DivideInstruction, Instruction, IntInstruction, MultiplyInstruction, NegateInstruction, SubtractInstruction, TernaryInstruction};
use crate::value::Type;
use crate::variable::Variable;

pub const COMPILER_TYPE_SCRIPT: u8 = 1;
pub const COMPILER_TYPE_EMPTY: u8 = 2;
pub const COMPILER_TYPE_EXPRESSION: u8 = 3;
pub const COMPILER_TYPE_INT: u8 = 4;
pub const COMPILER_TYPE_FLOAT: u8 = 5;
pub const COMPILER_TYPE_NEGATE: u8 = 6;
pub const COMPILER_TYPE_MATH: u8 = 7;
pub const COMPILER_TYPE_TERNARY: u8 = 8;
pub const COMPILER_TYPE_LET: u8 = 9;
pub const COMPILER_TYPE_IDENTIFIER: u8 = 10;
pub const COMPILER_TYPE_TYPE_DECLARATION: u8 = 11;

pub struct BlockType {
  pub names: HashMap<String, Variable>,
  pub code: Option<Arc<dyn Instruction>>,
}

pub struct Block
{
  pub names: HashMap<String, Variable>,
  pub parent: Option<Rc<RefCell<Block>>>,
}

impl Block {
  pub fn find_variable<F: Fn(Option<&mut Variable>) -> Option<CompileError>>(&mut self, name: &String, f: F) -> Option<CompileError> {
    match self.names.get_mut(name) {
      None => match self.parent.as_mut() {
        None => f(None),
        Some(p) => p.borrow_mut().find_variable(name, f),
      },
      Some(v) => f(Some(v)),
    }
  }
}

pub struct CompileContext {
  pub namespace: Rc<RefCell<Block>>,
}

pub struct CompileUml {
  pub object: Vec<String>,
  pub link: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum CompileError {
  Error(String),
}

impl fmt::Display for CompileError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      CompileError::Error(m) => write!(f, "{}", m),
    }
  }
}

impl Error for CompileError {
  #[allow(deprecated)]
  fn description(&self) -> &str {
    match *self {
      CompileError::Error(..) => "a compile error occurred",
    }
  }
}

pub trait Compiler: {
  fn pre_compile(
    &self,
    ctx: &mut CompileContext,
  ) -> Option<CompileError>;
  fn compile(
    &self,
    ctx: &mut CompileContext,
    next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError>;
  fn get_type(&self) -> u8;
  fn get_token(&self) -> Token;
  fn get_value_type(&self) -> Option<Type>;
  fn get_uml(&self, uml: &mut CompileUml) -> String;
  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError>;
  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError>;
  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>>;
  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>>;
  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>>;
}


pub struct ScriptCompiler {
  pub next: Option<Rc<RefCell<dyn Compiler>>>,
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for ScriptCompiler {
  fn pre_compile(&self, ctx: &mut CompileContext) -> Option<CompileError> {
    match &self.next {
      None => {}
      Some(e) => {
        e.as_ref().borrow().pre_compile(ctx);
      }
    }
    None
  }

  fn compile(
    &self,
    ctx: &mut CompileContext,
    next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    match self.next {
      Some(ref n) => { n.borrow().compile(ctx, None) }
      None => { Ok(next) }
    }
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> { None }
  fn get_uml(&self, uml: &mut CompileUml) -> String {
    match &self.next {
      None => { "".to_string() }
      Some(e) => {
        e.borrow().get_uml(uml)
      }
    }
  }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &None)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &None)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.next.as_ref()
  }
}


pub struct EmptyExpressionCompiler {
  pub next: Option<Rc<RefCell<dyn Compiler>>>,
  pub expression: Option<Rc<RefCell<dyn Compiler>>>,
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for EmptyExpressionCompiler {
  fn pre_compile(&self, _ctx: &mut CompileContext) -> Option<CompileError> { None }

  fn compile(
    &self,
    _ctx: &mut CompileContext,
    _next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    Ok(None)
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> { None }
  fn get_uml(&self, _uml: &mut CompileUml) -> String { String::from("") }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &None)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &None)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.next.as_ref()
  }
}

pub struct ExpressionCompiler {
  pub next: Option<Rc<RefCell<dyn Compiler>>>,
  pub expression: Option<Rc<RefCell<dyn Compiler>>>,
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for ExpressionCompiler {
  fn pre_compile(&self, ctx: &mut CompileContext) -> Option<CompileError> {
    match &self.expression {
      None => {}
      Some(e) => {
        e.as_ref().borrow().pre_compile(ctx);
      }
    }
    None
  }

  fn compile(
    &self,
    ctx: &mut CompileContext,
    next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    let n = match self.next {
      Some(ref n) => { n.borrow().compile(ctx, next)? }
      None => { next }
    };
    match &self.expression {
      None => {
        Ok(None)
      }
      Some(e) => {
        Ok(e.as_ref().borrow().compile(ctx, n)?)
      }
    }
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> { self.expression.as_ref().map_or(None, |c| { c.borrow().get_value_type() }) }
  fn get_uml(&self, uml: &mut CompileUml) -> String {
    String::from(match &self.expression {
      None => {
        ""
      }
      Some(e) => {
        e.as_ref().borrow().get_uml(uml);
        "expression{}"
      }
    })
  }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &None)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &None)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.next.as_ref()
  }
}


pub struct IntCompiler {
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for IntCompiler {
  fn pre_compile(&self, _ctx: &mut CompileContext) -> Option<CompileError> { None }

  fn compile(
    &self,
    _ctx: &mut CompileContext,
    next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    Ok(Some(Arc::new(IntInstruction {
      value: self.token.value.parse::<i32>().unwrap(),
      next,
      line: self.token.line,
      column: self.token.column,
    })))
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> { Some(Type::Int) }
  fn get_uml(&self, uml: &mut CompileUml) -> String {
    let name = format!("int_{}_{}", self.token.line, self.token.column);
    let object = format!("object {} {{\n\tvalue: {}\n}}", name, self.token.value);
    uml.object.push(object);
    return name;
  }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &None)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &None)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }
}

pub struct FloatCompiler {
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for FloatCompiler {
  fn pre_compile(&self, _ctx: &mut CompileContext) -> Option<CompileError> {
    todo!()
  }

  fn compile(
    &self,
    _ctx: &mut CompileContext,
    next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    Ok(Some(Arc::new(IntInstruction {
      value: self.token.value.parse::<i32>().unwrap(),
      next,
      line: self.token.line,
      column: self.token.column,
    })))
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> { Some(Type::Float) }
  fn get_uml(&self, uml: &mut CompileUml) -> String {
    let name = format!("float_{}_{}", self.token.line, self.token.column);
    let object = format!("object {} {{\n\tvalue: {}\n}}", name, self.token.value);
    uml.object.push(object);
    return name;
  }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &None)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &None)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }
}

pub struct NegateCompiler {
  pub right: Option<Rc<RefCell<dyn Compiler>>>,
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for NegateCompiler {
  fn pre_compile(&self, ctx: &mut CompileContext) -> Option<CompileError> {
    match &self.right {
      None => {}
      Some(e) => {
        e.as_ref().borrow().pre_compile(ctx);
      }
    }
    None
  }

  fn compile(
    &self,
    ctx: &mut CompileContext,
    next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    match self.right.as_ref().unwrap().borrow().get_value_type() {
      None => {
        return Err(CompileError::Error(format!("Unknown right element '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap()));
      }
      Some(ty) => {
        if ty != Type::Int && ty != Type::Float {
          return Err(CompileError::Error(format!("Right hand element can not be negated '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap()));
        }
      }
    };
    let i = Arc::new(NegateInstruction {
      next,
      line: self.token.line,
      column: self.token.column,
    });
    let r = self.right.as_ref().unwrap().borrow().compile(ctx, Some(i))?;
    Ok(r)
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> { self.right.as_ref().map_or(None, |c| { c.borrow().get_value_type() }) }
  fn get_uml(&self, uml: &mut CompileUml) -> String {
    let right = self.right.as_ref().unwrap().borrow().get_uml(uml);
    let name = format!("negate_{}_{}", self.token.line, self.token.column);
    let object = format!("object {} {{\n\tvalue: {}\n}}", name, self.token.value);
    let link_r = format!("{}-->{} : right", name, right);
    uml.object.push(object);
    uml.link.push(link_r);
    return name;
  }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &None)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &self.right)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.right.as_ref()
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }
}

pub struct MathCompiler {
  pub left: Option<Rc<RefCell<dyn Compiler>>>,
  pub right: Option<Rc<RefCell<dyn Compiler>>>,
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for MathCompiler {
  fn pre_compile(&self, ctx: &mut CompileContext) -> Option<CompileError> {
    match &self.left {
      None => {}
      Some(e) => {
        e.as_ref().borrow().pre_compile(ctx);
      }
    }
    match &self.right {
      None => {}
      Some(e) => {
        e.as_ref().borrow().pre_compile(ctx);
      }
    }
    None
  }

  fn compile(
    &self,
    ctx: &mut CompileContext,
    next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    match self.right.as_ref().unwrap().borrow().get_value_type() {
      None => {
        return Err(CompileError::Error(format!("Unknown right element '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap()));
      }
      Some(ty) => {
        if ty != Type::Int && ty != Type::Float {
          return Err(CompileError::Error(format!("Right hand element not math construct '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap()));
        }
      }
    };
    match self.left.as_ref().unwrap().borrow().get_value_type() {
      None => {
        return Err(CompileError::Error(format!("Unknown right element '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap()));
      }
      Some(ty) => {
        if ty != Type::Int && ty != Type::Float {
          return Err(CompileError::Error(format!("Right hand element not math construct '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap()));
        }
      }
    };
    let i: Arc<dyn Instruction> = match self.token.value.as_str() {
      "+" => { Arc::new(AddInstruction { next, line: self.token.line, column: self.token.column }) }
      "-" => { Arc::new(SubtractInstruction { next, line: self.token.line, column: self.token.column }) }
      "*" => { Arc::new(MultiplyInstruction { next, line: self.token.line, column: self.token.column }) }
      "/" => { Arc::new(DivideInstruction { next, line: self.token.line, column: self.token.column }) }
      _ => { Arc::new(AddInstruction { next, line: self.token.line, column: self.token.column }) } // this can (should) not happen
    };
    let r = self.right.as_ref().unwrap().borrow().compile(ctx, Some(i))?;
    let l = self.left.as_ref().unwrap().borrow().compile(ctx, r)?;
    Ok(l)
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> {
    let right = self.right.as_ref().map_or(Some(Type::Undefined), |c| { c.borrow().get_value_type() }).unwrap();
    let left = self.left.as_ref().map_or(Some(Type::Undefined), |c| { c.borrow().get_value_type() }).unwrap();
    Some(right.resolve_math_type(left))
  }
  fn get_uml(&self, uml: &mut CompileUml) -> String {
    let left = self.left.as_ref().unwrap().borrow().get_uml(uml);
    let right = self.right.as_ref().unwrap().borrow().get_uml(uml);
    let name = format!("math_{}_{}", self.token.line, self.token.column);
    let object = format!("object {} {{\n\tvalue: {}\n}}", name, self.token.value);
    let link_l = format!("{}-->{} : left", name, left);
    let link_r = format!("{}-->{} : right", name, right);
    uml.object.push(object);
    uml.link.push(link_l);
    uml.link.push(link_r);
    return name;
  }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &self.left)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &self.right)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.left.as_ref()
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.right.as_ref()
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }
}

pub struct TernaryCompiler {
  pub if_expression: Option<Rc<RefCell<dyn Compiler>>>,
  pub then_branch: Option<Rc<RefCell<dyn Compiler>>>,
  pub else_branch: Option<Rc<RefCell<dyn Compiler>>>,
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for TernaryCompiler {
  fn pre_compile(&self, ctx: &mut CompileContext) -> Option<CompileError> {
    match &self.if_expression {
      None => {}
      Some(e) => {
        e.as_ref().borrow().pre_compile(ctx);
      }
    }
    match &self.then_branch {
      None => {}
      Some(e) => {
        e.as_ref().borrow().pre_compile(ctx);
      }
    }
    match &self.else_branch {
      None => {}
      Some(e) => {
        e.as_ref().borrow().pre_compile(ctx);
      }
    }
    None
  }

  fn compile(
    &self,
    ctx: &mut CompileContext,
    next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    let tb = self.then_branch.as_ref().unwrap().borrow().compile(ctx, next.clone())?;
    let eb = self.else_branch.as_ref().unwrap().borrow().compile(ctx, next.clone())?;
    let bi = Arc::new(
      TernaryInstruction {
        instruction: self.token.value.chars().next().unwrap(),
        then_branch: tb,
        else_branch: eb,
        line: self.token.line,
        column: self.token.column,
      });
    let if_expression = self.if_expression.as_ref().unwrap().borrow().compile(ctx, Some(bi))?;
    Ok(Some(if_expression.unwrap()))
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> {
    let then_branch = self.then_branch.as_ref().map_or(Some(Type::Undefined), |c| { c.borrow().get_value_type() }).unwrap();
    let else_branch = self.else_branch.as_ref().map_or(Some(Type::Undefined), |c| { c.borrow().get_value_type() }).unwrap();
    Some(then_branch.resolve_math_type(else_branch))
  }
  fn get_uml(&self, uml: &mut CompileUml) -> String {
    let else_branch = self.else_branch.as_ref().unwrap().borrow().get_uml(uml);
    let then_branch = self.then_branch.as_ref().unwrap().borrow().get_uml(uml);
    let exp = self.if_expression.as_ref().unwrap().borrow().get_uml(uml);
    let name = format!("ternary_{}_{}", self.token.line, self.token.column);
    let object = format!("object {} {{\n\tvalue: {}\n}}", name, self.token.value);
    let link_exp = format!("{}-->{} : exp", name, exp);
    let link_then = format!("{}-->{} : then", name, then_branch);
    let link_else = format!("{}-->{} : else", name, else_branch);
    uml.object.push(object);
    uml.link.push(link_exp);
    uml.link.push(link_then);
    uml.link.push(link_else);
    return name;
  }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &None)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &None)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.if_expression.as_ref()
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.then_branch.as_ref()
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.else_branch.as_ref()
  }
}

pub struct IdentifierCompiler {
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for IdentifierCompiler {
  fn pre_compile(&self, _ctx: &mut CompileContext) -> Option<CompileError> { None }

  fn compile(
    &self,
    _ctx: &mut CompileContext,
    next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    Ok(Some(Arc::new(IntInstruction {
      value: self.token.value.parse::<i32>().unwrap(),
      next,
      line: self.token.line,
      column: self.token.column,
    })))
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> { Some(Type::Int) }
  fn get_uml(&self, uml: &mut CompileUml) -> String {
    let name = format!("ident_{}_{}", self.token.line, self.token.column);
    let object = format!("object {} {{\n\tvalue: {}\n}}\n", name, self.token.value);
    uml.object.push(object);
    return name;
  }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &None)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &None)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }
}

pub struct TypeCompiler {
  pub right: Option<Rc<RefCell<dyn Compiler>>>,
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for TypeCompiler {
  fn pre_compile(&self, _ctx: &mut CompileContext) -> Option<CompileError> { None }

  fn compile(
    &self,
    _ctx: &mut CompileContext,
    _next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    Ok(None)
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> { Some(Type::Int) }
  fn get_uml(&self, uml: &mut CompileUml) -> String {
    let name = format!("type_{}_{}", self.token.line, self.token.column);
    let object = format!("object {} {{\n\tvalue: {}\n}}\n", name, self.token.value);
    uml.object.push(object);
    return name;
  }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &None)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &None)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }
}

pub struct LetCompiler {
  pub right: Option<Rc<RefCell<dyn Compiler>>>,
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for LetCompiler {
  fn pre_compile(&self, ctx: &mut CompileContext) -> Option<CompileError> {
    self.right.as_ref().map_or_else(
      || Some(CompileError::Error(format!("No right hand component for LET '{}' at {}, {}", 
        self.token.value, self.token.line, self.token.column).into())),
      |c| {
        let borrowed = c.as_ref().borrow();
        if borrowed.get_type() == COMPILER_TYPE_IDENTIFIER {
          let token = borrowed.get_token();
          ctx.namespace.as_ref().borrow_mut()
            .names.insert(token.value.clone(),
                        Variable {
                          var_type: Type::Undefined,
                          name: token.value,
                        });
          None
        } else {
          Some(CompileError::Error(format!("Wrong right hand component for LET '{}' at {}, {}", 
            self.token.value, self.token.line, self.token.column).into()))
        }
      }
    )
  }

  fn compile(
    &self,
    ctx: &mut CompileContext,
    next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    self.right.as_ref()
      .ok_or_else(|| CompileError::Error("Missing right hand side in LET statement".into()))
      .and_then(|r| r.as_ref().borrow().compile(ctx, next))
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> {
    Some(self.right.as_ref().map_or(Some(Type::Undefined), |c| { c.borrow().get_value_type() }).unwrap())
  }
  fn get_uml(&self, uml: &mut CompileUml) -> String {
    let right = self.right.as_ref().unwrap().borrow().get_uml(uml);
    let name = format!("let_{}_{}", self.token.line, self.token.column);
    let object = format!("object {} {{\n\tvalue: {}\n}}", name, self.token.value);
    let link_r = format!("{}-->{} : right", name, right);
    uml.object.push(object);
    uml.link.push(link_r);
    return name;
  }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &None)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &self.right)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.right.as_ref()
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }
}

macro_rules! get_value_from_namespaces {
    ($name:expr, $namespace:expr, $work:expr, $fail:expr) => {
        match $namespace.as_ref().borrow_mut().names.get_mut($name) {
            Some(v) => {
                $work(v)
            }
            None => {
                let recurse = |po: &Option<Rc<RefCell<Block>>>|{
                    match po {
                        Some(p) => {
                            let mut pp = p.borrow_mut();
                            match pp.names.get_mut($name) {
                                None => {
                                    //recurse(&pp.parent)
                                    $fail()
                                }
                                Some(v) => {
                                    $work(v)
                                }
                            }
                        }
                        None => $fail()
                    }
                };
                recurse(&$namespace.as_ref().borrow_mut().parent)
            }
        }
    };
}


pub struct TypeOperatorCompiler {
  pub left: Option<Rc<RefCell<dyn Compiler>>>,
  pub right: Option<Rc<RefCell<dyn Compiler>>>,
  pub token: Token,
  pub compiler_type: u8,
}

impl Compiler for TypeOperatorCompiler {
  fn pre_compile(&self, ctx: &mut CompileContext) -> Option<CompileError> {
    match &self.right {
      None => {}
      Some(e ) => {
        e.as_ref().borrow().pre_compile(ctx);
      }
    }
    match &self.left {
      None => {}
      Some(e) => {
        e.as_ref().borrow().pre_compile(ctx);
      }
    }

    // match get_value_from_namespaces!("thing", ctx.namespace, |v:&mut Variable| {v.var_type = Type::Void; Ok(None::<Option<Variable>>)}, ||{
    //     Err(CompileError::Error(format!("Right hand component not found for type operator '{}' at {}, {}",self.token.value,self.token.line,self.token.column).parse().unwrap()))
    // }){
    //     Ok(_) => {}
    //     Err(_) => {}
    // };

    // ctx.namespace.as_ref().borrow_mut().find_variable(&"thing".to_string(), |v| {
    //     v.unwrap().var_type = Type::Void;
    //     None
    // });
    let set_type = self.get_right().map_or(
      Err(CompileError::Error(format!("No right hand type identifier '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap())),
      |tyrc| {
        let ty = tyrc.as_ref().borrow();
        match ty.get_token().value.as_str() {
          "int" => {
            Ok(Type::Int)
          }
          _ => {Err(CompileError::Error(format!("Type not recognized '{}' at {}, {}", ty.get_token().value, ty.get_token().line, ty.get_token().column).parse().unwrap()))}
        }
      },
    );

    let le = match self.get_left() {
      None => return Some(CompileError::Error(format!("No left hand component for type operator '{}' at {}, {}", self.token.value, self.token.line, self.token.column))),
      Some(lrc) => {
        lrc.as_ref().borrow()
      }
    };

    let attribute_to_compiler = match le.get_type() {
      COMPILER_TYPE_IDENTIFIER => {
        le
      }
      COMPILER_TYPE_LET => {
        // LET should have thrown an error if it doesn't have a right hand component
        le.get_right().unwrap().borrow()
      }
      _ => return Some(CompileError::Error(format!("Do not know how to assign Type to '{}' at {}, {}", le.get_token().value, le.get_token().line, le.get_token().column))),
    };

    return ctx.namespace.as_ref().borrow_mut().find_variable(&attribute_to_compiler.get_token().value, |vo| {
      vo.map_or(
        Some(CompileError::Error(format!("Left hand component not found for Type operator '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap())),
        |v| {
          if v.var_type == Type::Undefined {
            v.var_type = set_type.as_ref().unwrap().clone();
            None
          } else {
            Some(CompileError::Error(format!("Variable already has Type '{}' is '{}' at {}, {}", self.token.value, v.var_type.to_string(), self.token.line, self.token.column).parse().unwrap()))
          }
        }
      )
    });

/*
    let x = self.if_left(self.token.clone(), Box::new(|t, lo| {
      lo.as_ref().map_or(
        Some(CompileError::Error(format!("No left hand component for type operator '{}' at {}, {}", t.value, t.line, t.column))),
        |lrc| {
          let l = lrc.as_ref().borrow();
          match l.get_type() {
            COMPILER_TYPE_LET => {
              let lt = l.get_token().clone();
              //let rfn: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError>> = ;
              l.if_right(lt, Box::new(|t, rrc| {
                let r = rrc.as_ref().unwrap().borrow();
                match r.get_type() {
                  COMPILER_TYPE_IDENTIFIER => {
                    ctx.namespace.as_ref().borrow_mut().find_variable(&r.get_token().value, |vo| {
                      vo.map_or(
                        Some(CompileError::Error(format!("Left hand component not found for type operator '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap())),
                        |v| {
                          None
                        }
                      )
                    })
                  }
                  _ => {
                    Some(CompileError::Error(format!("Left hand component not target for Type '{}' at {}, {}", t.value, t.line, t.column).parse().unwrap()))
                  }
                }
              }))
            }
            _ => { Some(CompileError::Error(format!("No left hand component for Type operator '{}' at {}, {}", t.value, t.line, t.column))) }
          }
        })
    }));

    match self.left.as_ref() {
      None => { Some(CompileError::Error(format!("No left hand component for type operator '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap())) }
      Some(lrc) => {
        let le = lrc.as_ref().borrow();
        match le.get_type() {
          COMPILER_TYPE_LET => {
            match le.get_right() {
              Some(rrc) => {
                let ri = rrc.as_ref().borrow();
                match ri.get_type() {
                  COMPILER_TYPE_IDENTIFIER => {
                    ctx.namespace.as_ref().borrow_mut().find_variable(&ri.get_token().value, |vo| {
                      match vo {
                        None => Some(CompileError::Error(format!("Left hand component not found for type operator '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap())),
                        Some(v) => {
                          match self.left.as_ref() {
                            Some(re) => {
                              match re.as_ref().borrow().get_type() {
                                COMPILER_TYPE_IDENTIFIER => {
                                  v.var_type = Type::Void; // TODO: Determine actual type
                                  None
                                }
                                _ => Some(CompileError::Error(format!("Right hand component for type operator not found in namespace '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap())),
                              }
                            }
                            None => Some(CompileError::Error(format!("Right hand component not found for type operator '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap())),
                          }
                        }
                      }
                    })
                    //             Some(CompileError::Error(format!("Left hand component not found for type operator '{}' at {}, {}", token.value, token.line, token.column).parse().unwrap()))
                  }
                  _ => { Some(CompileError::Error(format!("Left hand component not Identifier '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap())) }
                }
              }
              _ => { Some(CompileError::Error(format!("Unknown left element for type '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap())) }
            }
          }
          // COMPILER_TYPE_IDENTIFIER => {
          //     match ctx.namespace.as_ref().borrow().names.get(&le.get_token().value) {
          //         None => {
          //             Some(CompileError::Error(format!("Left hand component not found for type operator '{}' at {}, {}",self.token.value,self.token.line,self.token.column).parse().unwrap()))
          //         }
          //         Some(n) => {
          //             None // TODO: assign type
          //         }
          //     }
          // }
          _ => { Some(CompileError::Error(format!("Left hand component not right for type operator '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap())) }
        }
      }
    }*/
  }

  fn compile(
    &self,
    ctx: &mut CompileContext,
    next: Option<Arc<dyn Instruction>>,
  ) -> Result<Option<Arc<dyn Instruction>>, CompileError> {
    match self.right.as_ref().unwrap().borrow().get_value_type() {
      None => {
        return Err(CompileError::Error(format!("Unknown right element '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap()));
      }
      Some(ty) => {
        if ty != Type::Int && ty != Type::Float {
          return Err(CompileError::Error(format!("Right hand element not type '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap()));
        }
      }
    };
    match self.left.as_ref().unwrap().borrow().get_value_type() {
      None => {
        return Err(CompileError::Error(format!("Unknown right element '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap()));
      }
      Some(ty) => {
        if ty != Type::Int && ty != Type::Float {
          return Err(CompileError::Error(format!("Right hand element not math construct '{}' at {}, {}", self.token.value, self.token.line, self.token.column).parse().unwrap()));
        }
      }
    };
    let i: Arc<dyn Instruction> = match self.token.value.as_str() {
      "+" => { Arc::new(AddInstruction { next, line: self.token.line, column: self.token.column }) }
      "-" => { Arc::new(SubtractInstruction { next, line: self.token.line, column: self.token.column }) }
      "*" => { Arc::new(MultiplyInstruction { next, line: self.token.line, column: self.token.column }) }
      "/" => { Arc::new(DivideInstruction { next, line: self.token.line, column: self.token.column }) }
      _ => { Arc::new(AddInstruction { next, line: self.token.line, column: self.token.column }) } // this can (should) not happen
    };
    let r = self.right.as_ref().unwrap().borrow().compile(ctx, Some(i))?;
    let l = self.left.as_ref().unwrap().borrow().compile(ctx, r)?;
    Ok(l)
  }
  fn get_type(&self) -> u8 { self.compiler_type }
  fn get_token(&self) -> Token { self.token.clone() }
  fn get_value_type(&self) -> Option<Type> {
    let right = self.right.as_ref().map_or(Some(Type::Undefined), |c| { c.borrow().get_value_type() }).unwrap();
    let left = self.left.as_ref().map_or(Some(Type::Undefined), |c| { c.borrow().get_value_type() }).unwrap();
    Some(right.resolve_math_type(left))
  }
  fn get_uml(&self, uml: &mut CompileUml) -> String {
    let left = self.left.as_ref().unwrap().borrow().get_uml(uml);
    let right = self.right.as_ref().unwrap().borrow().get_uml(uml);
    let name = format!("type_op_{}_{}", self.token.line, self.token.column);
    let object = format!("object {} {{\n\tvalue: {}\n}}", name, self.token.value);
    let link_l = format!("{}-->{} : left", name, left);
    let link_r = format!("{}-->{} : right", name, right);
    uml.object.push(object);
    uml.link.push(link_l);
    uml.link.push(link_r);
    return name;
  }

  fn if_left<'a>(&self, t: Token, left: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    left(t, &self.left)
  }

  fn if_right<'a>(&self, t: Token, right: Box<dyn Fn(Token, &Option<Rc<RefCell<dyn Compiler>>>) -> Option<CompileError> + 'a>) -> Option<CompileError> {
    right(t, &self.right)
  }

  fn get_left(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.left.as_ref()
  }

  fn get_right(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    self.right.as_ref()
  }

  fn get_next(&self) -> Option<&Rc<RefCell<dyn Compiler>>> {
    None
  }
}