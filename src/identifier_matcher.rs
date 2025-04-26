use std::collections::HashMap;

use lexx::matcher::{Matcher, MatcherResult};
use lexx::token::Token;

pub const TOKEN_TYPE_IDENTIFIER: u16 = 100;

#[derive(Clone, Debug, Copy)]
pub struct IdentifierMatcher {
  /// Current size of the ongoing match.
  pub index: usize,
  /// This matchers precedence.
  pub precedence: u8,
  /// If the matcher is currently running.
  pub running: bool,
}

impl Matcher for IdentifierMatcher {
  fn reset(&mut self, _ctx: &mut Box<HashMap<String, i32>>) {
    self.index = 0;
    self.running = true;
  }

  fn find_match(
    &mut self,
    oc: Option<char>,
    value: &[char],
    _ctx: &mut Box<HashMap<String, i32>>,
  ) -> MatcherResult {
    return match oc {
      None => {
        self.running = false;
        self.generate_identifier_token(value)
      }
      Some(c) => {
        if self.index == 0 {
          if c.is_alphabetic() || c == '_' {
            self.index += 1;
            MatcherResult::Running()
          } else {
            self.running = false;
            MatcherResult::Failed()
          }
        } else if c.is_alphabetic() || c.is_numeric() || c == '_' {
          self.index += 1;
          MatcherResult::Running()
        } else {
          self.running = false;
          self.generate_identifier_token(value)
        }
      }
    };
  }
  fn is_running(&self) -> bool {
    self.running
  }
  fn precedence(&self) -> u8 {
    self.precedence
  }
}

impl IdentifierMatcher {
  #[inline(always)]
  fn generate_identifier_token(&mut self, value: &[char]) -> MatcherResult {
    if self.index > 0 {
      MatcherResult::Matched(Token {
        value: value[0..self.index].into_iter().collect(),
        token_type: TOKEN_TYPE_IDENTIFIER,
        len: self.index,
        line: 0,
        column: self.index,
        precedence: self.precedence,
      })
    } else {
      MatcherResult::Failed()
    }
  }
}

#[cfg(test)]
mod tests {
  use lexx::{Lexx, Lexxer, LexxError};
  use lexx::input::InputString;

  use crate::identifier_matcher::{IdentifierMatcher, TOKEN_TYPE_IDENTIFIER};

  #[test]
  fn matcher_identifier_matches_word() {
    let mut lexx: Box<dyn Lexxer> = Box::new(Lexx::<512>::new(
      Box::new(InputString::new(String::from("The"))),
      vec![Box::new(IdentifierMatcher {
        index: 0,
        precedence: 0,
        running: true,
      })],
    ));

    match lexx.next_token() {
      Err(e) => match e {
        LexxError::TokenNotFound(_) => {
          assert!(false, "Should not have failed parsing file");
        }
        LexxError::Error(_) => {
          assert!(false, "Should not have failed parsing file");
        }
      },
      Ok(Some(t)) => {
        assert_eq!(t.value, "The");
        assert_eq!(t.token_type, TOKEN_TYPE_IDENTIFIER)
      }
      Ok(None) => {
        assert!(false, "Should not hit None");
      }
    }
  }

  #[test]
  fn matcher_identifier_matches_lead_underscore() {
    let mut lexx: Box<dyn Lexxer> = Box::new(Lexx::<512>::new(
      Box::new(InputString::new(String::from("_test"))),
      vec![Box::new(IdentifierMatcher {
        index: 0,
        precedence: 0,
        running: true,
      })],
    ));

    match lexx.next_token() {
      Err(e) => match e {
        LexxError::TokenNotFound(_) => {
          assert!(false, "Should not have failed parsing file");
        }
        LexxError::Error(_) => {
          assert!(false, "Should not have failed parsing file");
        }
      },
      Ok(Some(t)) => {
        assert_eq!(t.value, "_test");
        assert_eq!(t.token_type, TOKEN_TYPE_IDENTIFIER)
      }
      Ok(None) => {
        assert!(false, "Should not hit None");
      }
    }
  }

  #[test]
  fn matcher_identifier_matches_inner_underscore() {
    let mut lexx: Box<dyn Lexxer> = Box::new(Lexx::<512>::new(
      Box::new(InputString::new(String::from("test_this2"))),
      vec![Box::new(IdentifierMatcher {
        index: 0,
        precedence: 0,
        running: true,
      })],
    ));

    match lexx.next_token() {
      Err(e) => match e {
        LexxError::TokenNotFound(_) => {
          assert!(false, "Should not have failed parsing file");
        }
        LexxError::Error(_) => {
          assert!(false, "Should not have failed parsing file");
        }
      },
      Ok(Some(t)) => {
        assert_eq!(t.value, "test_this2");
        assert_eq!(t.token_type, TOKEN_TYPE_IDENTIFIER)
      }
      Ok(None) => {
        assert!(false, "Should not hit None");
      }
    }
  }

  #[test]
  fn matcher_identifier_does_not_match_lead_number() {
    let mut lexx = Lexx::<512>::new(
      Box::new(InputString::new(String::from("5test"))),
      vec![Box::new(IdentifierMatcher {
        index: 0,
        precedence: 0,
        running: true,
      })],
    );

    match lexx.next_token() {
      Err(e) => match e {
        LexxError::TokenNotFound(e) => {
          assert_eq!(e, "Could not resolve token at 1, 1: 'Some('5')'.");
        }
        LexxError::Error(_) => {
          assert!(false, "Should not get an error");
        }
      },
      Ok(_t) => {
        assert!(false, "should not have matched 5test");
      }
    }
  }
}