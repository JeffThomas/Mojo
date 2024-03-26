use crate::value::{Type};

#[derive(Debug, PartialEq, Clone)]
pub struct Variable {
    pub var_type: Type,
    pub name: String
}