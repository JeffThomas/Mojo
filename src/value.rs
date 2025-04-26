use std::collections::HashMap;
use std::fmt;

use crate::instruction::StupidInstructionBucket;
use crate::signature::Signature;

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
  Undefined,
  Void,
  Int,
  Float,
  String,
  Struct(Box<HashMap<String, Type>>),
  Option(Box<Type>),
  Result(Box<Type>, Box<Type>),
  Function(Signature),
  Instruction,
}

impl Type {
  pub fn to_string(&self) -> &str {
    match self {
      Type::Undefined => { "undefined" }
      Type::Void => { "void" }
      Type::Int => { "int"}
      Type::Float => { "float" }
      Type::String => { "string" }
      Type::Struct(_) => { "struct" }
      Type::Option(_) => { "option" }
      Type::Result(_, _) => { "result" }
      Type::Function(_) => { "function" }
      Type::Instruction => { "instruction" }
    }
  }

  // pub fn from_string(name: &str) -> Option<Type> {
  //   match name.to_lowercase().as_str() {
  //     "undefined" => Some(Type::Undefined),
  //     "void" => Some(Type::Void),
  //     "int" => Some(Type::Int),
  //     "float" => Some(Type::Float),
  //     "string" => Some(Type::String),
  //     "struct" => Some(Type::Struct()),
  //     "option" => Some(Type::Option()),
  //     "result" => Some(Type::Result()),
  //     "function" => Some(Type::Function()),
  //     "instruction" => Some(Type::Instruction),
  //   }
  // }

  pub fn resolve_math_type(&self, right: Type) -> Type {
    match self {
      Type::Undefined => {
        match right {
          Type::Undefined => { Type::Undefined }
          Type::Void => { Type::Void }
          Type::Int => { Type::Int }
          Type::Float => { Type::Float }
          Type::Option(o) => { Type::Option(o) }
          Type::Result(l, r) => { Type::Result(l, r) }
          Type::Function(t) => { Type::Function(t) }
          Type::Instruction => { Type::Instruction }
          Type::Struct(s) => { Type::Struct(s) }
          Type::String => { Type::String }
        }
      }
      Type::Void => {
        match right {
          Type::Undefined => { Type::Void }
          Type::Void => { Type::Void }
          Type::Int => { Type::Int }
          Type::Float => { Type::Float }
          Type::Option(o) => { Type::Option(o) }
          Type::Result(l, r) => { Type::Result(l, r) }
          Type::Function(t) => { Type::Function(t) }
          Type::Instruction => { Type::Instruction }
          Type::Struct(s) => { Type::Struct(s) }
          Type::String => { Type::String }
        }
      }
      Type::Int => {
        match right {
          Type::Undefined => { Type::Int }
          Type::Void => { Type::Int }
          Type::Int => { Type::Int }
          Type::Float => { Type::Float }
          Type::Option(o) => { o.resolve_math_type(Type::Int) }
          Type::Result(l, r) => { Type::Result(l, r) }
          Type::Function(t) => { Type::Function(t) }
          Type::Instruction => { Type::Instruction }
          Type::Struct(s) => { Type::Struct(s) }
          Type::String => { Type::Int }
        }
      }
      Type::Float => {
        match right {
          Type::Undefined => { Type::Float }
          Type::Void => { Type::Float }
          Type::Int => { Type::Float }
          Type::Float => { Type::Float }
          Type::Option(o) => { o.resolve_math_type(Type::Float) }
          Type::Result(l, r) => { Type::Result(l, r) }
          Type::Function(t) => { Type::Function(t) }
          Type::Instruction => { Type::Instruction }
          Type::Struct(s) => { Type::Struct(s) }
          Type::String => { Type::Float }
        }
      }
      Type::Option(o) => {
        match right {
          Type::Undefined => { Type::Option(o.clone()) }
          Type::Void => { Type::Option(o.clone()) }
          Type::Int => { o.resolve_math_type(Type::Int) }
          Type::Float => { o.resolve_math_type(Type::Float) }
          Type::Option(oo) => { o.resolve_math_type(oo.as_ref().clone()) }
          Type::Result(l, r) => { Type::Result(l, r) }
          Type::Function(t) => { Type::Function(t) }
          Type::Instruction => { Type::Instruction }
          Type::Struct(s) => { Type::Struct(s) }
          Type::String => { Type::Option(Box::new(o.resolve_math_type(Type::String))) }
        }
      }
      Type::Result(l, r) => {
        match right {
          Type::Undefined => { Type::Result(Box::new(l.as_ref().clone()), Box::new(r.as_ref().clone())) }
          Type::Void => { Type::Result(Box::new(l.as_ref().clone()), Box::new(r.as_ref().clone())) }
          Type::Int => { Type::Result(Box::new(l.as_ref().clone()), Box::new(r.as_ref().clone())) }
          Type::Float => { Type::Result(Box::new(l.as_ref().clone()), Box::new(r.as_ref().clone())) }
          Type::Option(o) => { Type::Result(Box::new(o.resolve_math_type(l.as_ref().clone())), Box::new(r.as_ref().clone())) }
          Type::Result(ll, rr) => { Type::Result(Box::new(ll.resolve_math_type(l.as_ref().clone())), Box::new(rr.as_ref().clone())) }
          Type::Function(t) => { Type::Function(t) }
          Type::Instruction => { Type::Instruction }
          Type::Struct(s) => { Type::Struct(s) }
          Type::String => { Type::Result(Box::new(Type::String), Box::new(r.as_ref().clone())) }
        }
      }
      Type::Function(o) => {
        match right {
          Type::Undefined => { Type::Function(o.clone()) }
          Type::Void => { Type::Function(o.clone()) }
          Type::Int => { Type::Function(o.clone()) }
          Type::Float => { Type::Function(o.clone()) }
          Type::Option(_) => { Type::Function(o.clone()) }
          Type::Result(_, _) => { Type::Function(o.clone()) }
          Type::Function(_) => { Type::Function(o.clone()) }
          Type::Instruction => { Type::Instruction }
          Type::Struct(s) => { Type::Struct(s) }
          Type::String => { Type::Function(o.clone()) }
        }
      }
      Type::Instruction => {
        match right {
          Type::Undefined => { Type::Undefined }
          Type::Void => { Type::Void }
          Type::Int => { Type::Int }
          Type::Float => { Type::Float }
          Type::Option(o) => { Type::Option(o) }
          Type::Result(r, l) => { Type::Result(r, l) }
          Type::Function(o) => { Type::Function(o) }
          Type::Instruction => { Type::Instruction }
          Type::Struct(s) => { Type::Struct(s) }
          Type::String => { Type::Instruction }
        }
      }
      Type::Struct(_) => {
        match right {
          Type::Undefined => { Type::Undefined }
          Type::Void => { Type::Void }
          Type::Int => { Type::Int }
          Type::Float => { Type::Float }
          Type::Option(o) => { Type::Option(o) }
          Type::Result(r, l) => { Type::Result(r, l) }
          Type::Function(o) => { Type::Function(o) }
          Type::Instruction => { Type::Instruction }
          Type::Struct(s) => { Type::Struct(s) }
          Type::String => { Type::String }
        }
      }
      Type::String => {
        match right {
          Type::Undefined => { Type::String }
          Type::Void => { Type::String }
          Type::Int => { Type::String }
          Type::Float => { Type::String }
          Type::Option(_) => { Type::Option(Box::new(Type::String)) }
          Type::Result(l, r) => { Type::Result(l, r) }
          Type::Function(t) => { Type::Function(t) }
          Type::Instruction => { Type::String }
          Type::Struct(s) => { Type::Struct(s) }
          Type::String => { Type::String }
        }
      }
    }
  }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
  Undefined(),
  Int(i32),
  Float(f32),
  Option(Option<Box<Value>>),
  Result(Result<Box<Value>, Box<Value>>),
  Instruction(StupidInstructionBucket),
}

impl fmt::Display for Value {
  fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Value::Undefined() => {
        write!(out, "Undefined!")
      }
      Value::Int(i) => {
        write!(out, "{}", i)
      }
      Value::Float(f) => {
        write!(out, "{:.32}", f)
      }
      Value::Option(o) => {
        match o {
          None => { write!(out, "None") }
          Some(s) => { write!(out, "Some({})", s) }
        }
      }
      Value::Result(r) => {
        match r {
          Ok(o) => { write!(out, "Ok({})", o) }
          Err(e) => { write!(out, "Err({})", e) }
        }
      }
      Value::Instruction(_i) => {
        write!(out, "Instruction")
      }
    }
  }
}

impl Value {}
