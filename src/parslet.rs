use std::cell::RefCell;
use std::rc::Rc;

use lexx::matcher_whitespace::TOKEN_TYPE_WHITESPACE;
use lexx::token::Token;

use crate::compiler::{Compiler, ExpressionCompiler};
use crate::parser::{ParseContext, ParseError, Parser};

/// The Pratt parser pattern only has two kinds of Parslets, Prefix and Infix. Items that
/// stand alone, such as a simple number, are considered Prefix Parslets that don't consume
/// any right hand components. This is about as simple as a Parslet gets
pub struct PrefixParslet {
    /// the `matcher` function evaluates a token and decides if this parslet will parse it
    /// if `matcher` returns `true` then the `generator` function will be called to do the parsing
    pub matcher: fn(
        // The context can be used for state information during parsing
        ctx: &mut ParseContext,
        // The token is what is to be parsed
        token: &Token
    ) -> bool,
    /// the `generator` function creates a [Compiler](crate::compiler::Compiler) based on the Token
    pub generator: fn(
        // The context can be used for state information during parsing
        ctx: &mut ParseContext,
        // The token is what is to be parsed
        token: &Token,
    ) -> Result<Option<Rc<RefCell<dyn Compiler>>>, ParseError>,
}

/// A collection of utility functions for Parsing
impl PrefixParslet {
    /// A utility function that simply calls `matcher` on the parslet and if it returns
    /// `true`, calls `generator`.
    pub fn parse(
        &self,
        ctx: &mut ParseContext,
        token: &Token,
        _left: &Option<Rc<RefCell<dyn Compiler>>>,
        _precedence: u8,
    ) -> Result<Option<Rc<RefCell<dyn Compiler>>>, ParseError> {
        if (self.matcher)(ctx, token) {
            (self.generator)(ctx, token)
        } else {
            Ok(None)
        }
    }
    /// Recursively parse expressions and chain them together.
    /// Chain parse is for handling expression chains,  `x = 2; if x < 3 then x + 3` is tree
    /// top level expressions one of which contains a sub expressions. This could be represented in
    /// the compiler tree as something like
    ///```text
    ///             =  --------  <  --------- if
    ///           /  \         /   \            \
    ///         x     2       x    3             +
    ///                                        /   \
    ///                                       x     3
    ///```
    /// (NOTE, this is just one way to implement `if then`)
    /// Those '----------' lines are made with `chain_parse` in conjunction with the
    /// `script_parser` and `sub_parser` example Parslets.
    pub fn chain_parse(ctx: &mut ParseContext) -> Result<Option<Rc<RefCell<dyn Compiler>>>, ParseError> {
        let current = Parser::parse(ctx, &None, 0)?;
        return match current.as_ref() {
            None => Ok(None),
            Some(_) => {
                let next = PrefixParslet::chain_parse(ctx)?;
                Ok(Some(Rc::new(RefCell::new(ExpressionCompiler {
                    next,
                    expression: current,
                    token: Token { value: "".to_string(), token_type: 0, len: 0, line: 0, column: 0, precedence: 0, },
                    compiler_type: 0,
                }))))
            }
        };
    }
    /// Recursively parse expressions and chain them together until a particular token is found.
    /// Like `chain_parse` above this is for handling expressions chains, but this is
    /// specifically for parsing blocks, such as `{x = 2; if x < 3 then x + 3}` it is used
    /// by the `sub_parser` example Parslet.
    pub fn chain_parse_until_token(
        ctx: &mut ParseContext,
        token: &Token,
    ) -> Result<Option<Rc<RefCell<dyn Compiler>>>, ParseError> {
        let mut lh = ctx.lexx.look_ahead();
        if lh.as_ref().is_ok() && lh.as_ref().unwrap().as_ref().unwrap().token_type == TOKEN_TYPE_WHITESPACE {
            _ = ctx.lexx.next_token();
            lh = ctx.lexx.look_ahead();
        }
        match lh {
            Ok(Some(t)) => {
                if t.token_type == token.token_type && t.value == token.value {
                    // burn off the block end token
                    let _ = ctx.lexx.next_token();
                    return Ok(None);
                }
            }
            _ => {}
        }
        let current = Parser::parse(ctx, &None, 0)?;
        return match current.as_ref() {
            None => Ok(None),
            Some(_) => {
                let next = PrefixParslet::chain_parse_until_token(ctx, token)?;
                Ok(Some(Rc::new(RefCell::new(ExpressionCompiler {
                    next,
                    expression: current,
                    token: Token { value: "".to_string(), token_type: 0, len: 0, line: 0, column: 0, precedence: 0, },
                    compiler_type: 0,
                }))))
            }
        };
    }
}

/// The InfixParslet which is used to parse operators such as '+'.
/// It typically gets handed the previously parsed Token in the form of an already created
/// Compiler for it's left hand element, and then it recursively parses the next Token
/// to get it's right hand component.
pub struct InfixParslet {
    /// Precedence insures the orders of operation are followed
    /// For an in-depth look at how they work check the docs for the Parser
    pub precedence: u8,
    /// the `matcher` function evaluates a token and decides if this parslet will parse it
    /// in this case it needs to take the precedence of any previous infix parslets into
    /// consideration. Again, for an in-depth look at how precedence works check the Parser
    /// if `matcher` returns `true` then the `generator` function will be called to do the parsing
    pub matcher: fn(ctx: &mut ParseContext, token: &Token, precedence: u8, left: &Option<Rc<RefCell<dyn Compiler>>>) -> bool,
    // the `generator` function creates a Compiler from this Parslet
    // the 'left' parameter here would represent the left hand componant, or the '1' in the
    // expression '1 + 5'.
    pub generator: fn(
        ctx: &mut ParseContext,
        token: &Token,
        left: &Option<Rc<RefCell<dyn Compiler>>>,
        precedence: u8,
    ) -> Result<Option<Rc<RefCell<dyn Compiler>>>, ParseError>,
}
impl InfixParslet {
    /// A utility function that simply calls `matcher` on the parslet and if it returns
    /// `true`, calls `generator`.
    pub fn parse(
        &self,
        ctx: &mut ParseContext,
        token: &Token,
        left: &Option<Rc<RefCell<dyn Compiler>>>,
        precedence: u8,
    ) -> Result<Option<Rc<RefCell<dyn Compiler>>>, ParseError> {
        if (self.matcher)(ctx, token, precedence, left) {
            (self.generator)(ctx, token, left, self.precedence)
        } else {
            Ok(None)
        }
    }
}
