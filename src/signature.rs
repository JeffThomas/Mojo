use std::collections::HashMap;

use crate::variable::Variable;

#[derive(Debug, PartialEq, Clone)]
pub struct Signature {
  pub params: Vec<Variable>,
  pub captures: Vec<Variable>,
  pub public: Vec<Variable>,
  pub methods: HashMap<String, Signature>,
}