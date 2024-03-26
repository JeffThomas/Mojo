use std::collections::HashMap;
use std::fmt;
use crate::instruction::{StupidInstructionBucket};
use crate::signature::Signature;

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Undefined,
    Void,
    Int,
    Float,
    Struct(Box<HashMap<String,Type>>),
    Option(Box<Type>),
    Result(Box<Type>, Box<Type>),
    Function(Signature),
    Instruction,
}

impl Type {
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
                    Type::Struct(s) => {Type::Struct(s)}
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
                    Type::Struct(s) => {Type::Struct(s)}
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
                    Type::Struct(s) => {Type::Struct(s)}
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
                    Type::Struct(s) => {Type::Struct(s)}
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
                    Type::Struct(s) => {Type::Struct(s)}
                }
            }
            Type::Result(l, r) => {
                match right {
                    Type::Undefined => { Type::Result(Box::new(l.as_ref().clone()), Box::new(r.as_ref().clone())) }
                    Type::Void => { Type::Result(Box::new(l.as_ref().clone()), Box::new(r.as_ref().clone())) }
                    Type::Int => { Type::Result(Box::new(l.as_ref().clone()), Box::new(r.as_ref().clone())) }
                    Type::Float => { Type::Result(Box::new(l.as_ref().clone()), Box::new(r.as_ref().clone())) }
                    Type::Option(_) => { Type::Result(Box::new(l.as_ref().clone()), Box::new(r.as_ref().clone())) }
                    Type::Result(l, r) => { Type::Result(Box::new(l.as_ref().clone()), Box::new(r.as_ref().clone())) }
                    Type::Function(t) => { Type::Function(t) }
                    Type::Instruction => { Type::Instruction }
                    Type::Struct(s) => {Type::Struct(s)}
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
                    Type::Struct(s) => {Type::Struct(s)}
                }
            }
            Type::Instruction => {
                match right {
                    Type::Undefined => { Type::Undefined }
                    Type::Void => { Type::Void }
                    Type::Int => { Type::Int }
                    Type::Float => { Type::Float }
                    Type::Option(o) => { Type::Option(o) }
                    Type::Result(r, l) => { Type::Result(r,l) }
                    Type::Function(o) => { Type::Function(o) }
                    Type::Instruction => { Type::Instruction }
                    Type::Struct(s) => {Type::Struct(s)}
                }
            }
            Type::Struct(_) => {
                match right {
                    Type::Undefined => { Type::Undefined }
                    Type::Void => { Type::Void }
                    Type::Int => { Type::Int }
                    Type::Float => { Type::Float }
                    Type::Option(o) => { Type::Option(o) }
                    Type::Result(r, l) => { Type::Result(r,l) }
                    Type::Function(o) => { Type::Function(o) }
                    Type::Instruction => { Type::Instruction }
                    Type::Struct(s) => {Type::Struct(s)}
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
    Result(Result<Box<Value>,Box<Value>>),
    Instruction(StupidInstructionBucket)
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
