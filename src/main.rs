use std::cell::RefCell;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::stdin;
use std::rc::Rc;
use std::sync::Arc;

use clap::Parser as CliParser;
use lexx::input::{InputReader, InputString, LexxInput};
use lexx::Lexx;
use lexx::matcher_exact::ExactMatcher;
use lexx::matcher_integer::IntegerMatcher;
use lexx::matcher_keyword::KeywordMatcher;
use lexx::matcher_whitespace::WhitespaceMatcher;
use lexx::token::{Token, TOKEN_TYPE_FLOAT, TOKEN_TYPE_INTEGER, TOKEN_TYPE_KEYWORD, TOKEN_TYPE_WHITESPACE};

use crate::compiler::{CompileContext, CompileError, Compiler, COMPILER_TYPE_FLOAT, COMPILER_TYPE_IDENTIFIER, COMPILER_TYPE_INT, COMPILER_TYPE_LET, COMPILER_TYPE_MATH, COMPILER_TYPE_NEGATE, COMPILER_TYPE_TERNARY, COMPILER_TYPE_TYPE_DECLARATION, CompileUml, FloatCompiler, IdentifierCompiler, IntCompiler, LetCompiler, MathCompiler, Block, NegateCompiler, TernaryCompiler, TypeCompiler, TypeOperatorCompiler};
use crate::identifier_matcher::{IdentifierMatcher, TOKEN_TYPE_IDENTIFIER};
use crate::instruction::{ExecutionContext, Instruction};
use crate::parser::{ParseContext, ParseError, Parser, PRECEDENCE_CALL, PRECEDENCE_CONDITIONAL, PRECEDENCE_EXPONENT, PRECEDENCE_PREFIX, PRECEDENCE_PRODUCT, PRECEDENCE_SUM};
use crate::parslet::{InfixParslet, PrefixParslet};

pub mod compiler;
pub mod instruction;
pub mod parser;
pub mod parslet;
pub mod value;
pub mod identifier_matcher;
pub mod block;
pub mod variable;
pub mod signature;

pub const TOKEN_TYPE_OPERATOR: u16 = 20;
pub const TOKEN_TYPE_TYPE_DECLARATION: u16 = 21;

#[derive(CliParser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Name of file to parse
    #[arg(short, long, default_value_t = String::from(""))]
    file: String,
    #[arg(default_value_t = String::from(""))]
    raw: String,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum MojoError {
    Error(String),
}

impl fmt::Display for MojoError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MojoError::Error(m) => write!(f, "{}", m),
        }
    }
}

impl Error for MojoError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        match *self {
            MojoError::Error(..) => "a compile error occurred",
        }
    }
}

impl From<CompileError> for MojoError {
    fn from(le: CompileError) -> MojoError {
        match le {
            CompileError::Error(m) => {
                MojoError::Error(m)
            }
        }
    }
}

impl From<ParseError> for MojoError {
    fn from(le: ParseError) -> MojoError {
        match le {
            ParseError::Error(m) => {
                MojoError::Error(m)
            }
            ParseError::TokenNotFound(m) => {
                MojoError::Error(m)
            }
            ParseError::NoParserFound(t) => {
                MojoError::Error(format!("Missing '{}' at {}, {}",t.value,t.line,t.column))
            }
        }
    }
}

pub fn make_parse_context(input: Box<dyn LexxInput>) -> ParseContext {
    let eoe_parslet = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_OPERATOR
                && ";" == token.value { true } else { false }},
        generator: |ctx, _token| {
            Parser::parse(ctx, &None, 0)
        },
    };

    let int_parslet = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_INTEGER { true } else { false }
        },
        generator: |_ctx, token| {
            Ok(Some(Rc::new(RefCell::new(IntCompiler {
                token: token.clone(),
                compiler_type: COMPILER_TYPE_INT,
            }))))
        },
    };

    let float_parslet = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_FLOAT { true } else { false }
        },
        generator: |_ctx, token| {
            Ok(Some(Rc::new(RefCell::new(FloatCompiler {
                token: token.clone(),
                compiler_type: COMPILER_TYPE_FLOAT,
            }))))
        },
    };

    let negate_parslet = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_OPERATOR
                && "-" == token.value { true } else { false }},
        generator: |ctx, token| {
            let right = Parser::parse(ctx, &None, PRECEDENCE_PREFIX)?;
            Ok(Some(Rc::new(RefCell::new(NegateCompiler {
                right,
                token: token.clone(),
                compiler_type: COMPILER_TYPE_NEGATE,
            }))))
        },
    };

    let div_operator = InfixParslet {
        precedence: PRECEDENCE_PRODUCT,
        matcher: |_ctx, token, precedence, _left| {
            if precedence < PRECEDENCE_PRODUCT
                && token.token_type == TOKEN_TYPE_OPERATOR
                && "/" == token.value { true } else { false }},
        generator: |ctx, token, left, precedence| {
            let right = Parser::parse(ctx, left, precedence)?;
            Ok(Some(Rc::new(RefCell::new(MathCompiler {
                left: left.as_ref().map(|l| l.clone()),
                right,
                token: token.clone(),
                compiler_type: COMPILER_TYPE_MATH,
            }))))
        },
    };

    let mult_operator = InfixParslet {
        precedence: PRECEDENCE_PRODUCT,
        matcher: |_ctx, token, precedence, _left| {
            if precedence < PRECEDENCE_PRODUCT
                && token.token_type == TOKEN_TYPE_OPERATOR
                && "*" == token.value { true } else { false }},
        generator: |ctx, token, left, precedence| {
            let right = Parser::parse(ctx, left, precedence)?;
            Ok(Some(Rc::new(RefCell::new(MathCompiler {
                left: left.as_ref().map(|l| l.clone()),
                right,
                token: token.clone(),
                compiler_type: COMPILER_TYPE_MATH,
            }))))
        },
    };

    let plus_operator = InfixParslet {
        precedence: PRECEDENCE_SUM,
        matcher: |_ctx, token, precedence, _left| {
            if precedence < PRECEDENCE_SUM
                && token.token_type == TOKEN_TYPE_OPERATOR
                && "+" == token.value { true } else { false }},
        generator: |ctx, token, left, precedence| {
            let right = Parser::parse(ctx, left, precedence)?;
            Ok(Some(Rc::new(RefCell::new(MathCompiler {
                left: left.as_ref().map(|l| l.clone()),
                right,
                token: token.clone(),
                compiler_type: COMPILER_TYPE_MATH,
            }))))
        },
    };

    let minus_operator = InfixParslet {
        precedence: PRECEDENCE_SUM,
        matcher: |_ctx, token, precedence, _left| {
            if precedence < PRECEDENCE_SUM
                && token.token_type == TOKEN_TYPE_OPERATOR
                && "-" == token.value { true } else { false }},
        generator: |ctx, token, left, precedence| {
            let right = Parser::parse(ctx, left, precedence)?;
            Ok(Some(Rc::new(RefCell::new(MathCompiler {
                left: left.as_ref().map(|l| l.clone()),
                right,
                token: token.clone(),
                compiler_type: COMPILER_TYPE_MATH,
            }))))
        },
    };

    let ternary_parslet = InfixParslet {
        precedence: PRECEDENCE_CALL,
        matcher: |_ctx, token, precedence, _left| {
            if precedence < PRECEDENCE_CALL
                && token.token_type == TOKEN_TYPE_OPERATOR
                && token.value == "?" {true} else {false}
        },

        generator: |ctx, token, left, precedence| {
            let then_branch = Parser::parse(ctx, &None, precedence)?;
            eat_token_or_throw_error!(ctx, TOKEN_TYPE_OPERATOR, ":");
            let else_branch = Parser::parse(ctx, &None, precedence)?;
            Ok(Some(Rc::new(RefCell::new(TernaryCompiler {
                compiler_type: COMPILER_TYPE_TERNARY,
                if_expression: left.as_ref().map(|l|{l.clone()}),
                then_branch: then_branch.map(|r:Rc<RefCell<dyn Compiler>>|{r}),
                else_branch: else_branch.map(|r:Rc<RefCell<dyn Compiler>>|{r}),
                token: token.clone(),
            }))))
        }
    };

    let sub_parser = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_OPERATOR && "(" == token.value {
                true
            } else {
                false
            }
        },
        generator: |ctx, _token| {
            return PrefixParslet::chain_parse_until_token(
                ctx,
                &Token {
                    value: ")".to_string(),
                    token_type: TOKEN_TYPE_OPERATOR,
                    len: 0,
                    line: 0,
                    column: 0,
                    precedence: 0,
                },
            );
        },
    };

    let identifier_parslet = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_IDENTIFIER { true } else { false }
        },
        generator: |_ctx, token| {
            Ok(Some(Rc::new(RefCell::new(IdentifierCompiler {
                token: token.clone(),
                compiler_type: COMPILER_TYPE_IDENTIFIER,
            }))))
        },
    };

    let type_parslet = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_TYPE_DECLARATION { true } else { false }
        },
        generator: |_ctx, token| {
            Ok(Some(Rc::new(RefCell::new(TypeCompiler {
                token: token.clone(),
                compiler_type: COMPILER_TYPE_TYPE_DECLARATION,
            }))))
        },
    };

    let type_operator = InfixParslet {
        precedence: PRECEDENCE_CONDITIONAL,
        matcher: |_ctx, token, precedence, left| {
            if precedence >= PRECEDENCE_CONDITIONAL
                || ":" != token.value
                || left.is_none()
                || token.token_type != TOKEN_TYPE_OPERATOR { return false; }
            let left_type = left.as_ref().unwrap().borrow().get_type();
            (left_type == COMPILER_TYPE_IDENTIFIER)
                || (left_type == COMPILER_TYPE_LET)
        },
        generator: |ctx, token, left, precedence| {
            let right = Parser::parse(ctx, left, precedence)?;
            Ok(Some(Rc::new(RefCell::new(TypeOperatorCompiler {
                left: left.as_ref().map(|l| l.clone()),
                right,
                token: token.clone(),
                compiler_type: COMPILER_TYPE_TYPE_DECLARATION,
            }))))
        },
    };

    let let_parser = PrefixParslet {
        matcher: |_ctx, token| {
            if token.token_type == TOKEN_TYPE_KEYWORD && "let" == token.value { true } else { false }
        },
        generator: |ctx, token| {
            let right = Parser::parse(ctx, &None, PRECEDENCE_EXPONENT)?;

            match right {
                None => {
                    return Err(ParseError::Error(format!("Unexpected end of file")));
                }
                Some(r) => {
                    let t = r.as_ref().borrow().get_type();
                    if t != COMPILER_TYPE_IDENTIFIER
                        && t != COMPILER_TYPE_TYPE_DECLARATION {
                        return Err(ParseError::Error(format!("Cannot 'let' '{}' at {}, {}",token.value,token.line,token.column).parse().unwrap()))
                    }
                    Ok(Some(Rc::new(RefCell::new(LetCompiler {
                        right: Some(r),
                        token: token.clone(),
                        compiler_type: COMPILER_TYPE_LET,
                    }))))
                }
            }
        },
    };

///////////////////////////////////////////////////////////////////////////////////
//
// ParseContext
//
///////////////////////////////////////////////////////////////////////////////////

    return ParseContext {
        lexx: Box::new(Lexx::<512>::new(
            input,
            vec![
                Box::new(KeywordMatcher::build_matcher_keyword(vec!["let", "const"], TOKEN_TYPE_KEYWORD, 1)),
                Box::new(KeywordMatcher::build_matcher_keyword(vec!["number"], TOKEN_TYPE_TYPE_DECLARATION, 1)),
                Box::new(IdentifierMatcher { index: 0, precedence: 0, running: false, }),
                Box::new(IntegerMatcher { index: 0, precedence: 0, running: true, }),
                Box::new(WhitespaceMatcher { index: 0, column: 0, line: 0, precedence: 0, running: true, }),
                Box::new(ExactMatcher::build_exact_matcher(
                    vec!["+", "-", "*", "/", "(", ")", ";","?",":"],
                    TOKEN_TYPE_OPERATOR,
                    1,
                )),
            ],
        )),
        prefix: vec![
            negate_parslet,
            int_parslet,
            float_parslet,
            sub_parser,
            eoe_parslet,
            let_parser,
            identifier_parslet,
            type_parslet
        ],
        infix: vec![
            plus_operator,
            minus_operator,
            mult_operator,
            div_operator,
            ternary_parslet,
            type_operator
        ],
        script_name: "test.txt".to_string(),
    };

}

pub fn execute_instructions(instruction: Arc<dyn Instruction>) -> Result<ExecutionContext, MojoError> {
    let mut ctx = ExecutionContext { stack: Vec::new() };


    let mut running_instruction: Result<Option<Arc<dyn Instruction>>, MojoError> = Ok(Some(instruction));

    loop {
        match running_instruction {
            Ok(Some(i)) => {
                running_instruction = i.execute(&mut ctx);
            }
            Ok(None) => {
                return Ok(ctx);
            }
            Err(e) => {
                return Err(e);
            }
        }
    }
}

pub fn run_script(parse_context: &mut ParseContext) -> Result<ExecutionContext, MojoError> {

    let parse_result = PrefixParslet::chain_parse(parse_context)?;

    let compiler = parse_result.unwrap();
    let compile_result = compiler.borrow().compile(&mut CompileContext {namespace:Rc::new(RefCell::new(Block {
        names: HashMap::new(),
        parent: None,
    }))}, None)?;

    if compile_result.is_none() {
        return Ok(ExecutionContext{ stack: vec![] });
    }

    execute_instructions(compile_result.unwrap())
}

pub fn collect_uml(parse_context: &mut ParseContext) -> Result<String, MojoError> {
    let parse_result = PrefixParslet::chain_parse(parse_context)?;
    let compiler = parse_result.unwrap();
    let mut uml_ctx = &mut CompileUml { object: vec![], link: vec![] };
    let comp_ctx = &mut CompileContext {namespace:Rc::new(RefCell::new(Block {
        names: HashMap::new(),
        parent: None,
    }))};
    let err = compiler.borrow().pre_compile(comp_ctx);
    if err.is_some() {
        println!("{}", err.unwrap().to_string())
    }
    let _root_obj = compiler.borrow().get_uml(&mut uml_ctx);
    let mut uml = String::from("@startuml\n");
    for o in &uml_ctx.object {
        uml = format!("{}\n{}", uml, o);
    }
    uml = format!("{}\n", uml);
    for o in &uml_ctx.link {
        uml = format!("{}\n{}", uml, o);
    }
    uml = format!("{}\n@enduml", uml);

    return Ok(uml);
}

fn main() {
    let args = Args::parse();

    let input: Box<dyn LexxInput> = if args.file != "" {
        let file = File::open(args.file).unwrap();
        Box::new(InputReader::new(file))
    } else if args.raw != "" {
        Box::new(InputString::new(args.raw))
    } else {
        let input_stdin = InputReader::new(stdin());
        Box::new(input_stdin)
    };

    let mut pc = make_parse_context(input);

    let run_result = run_script(&mut pc);

    let mut ctx = match run_result {
        Ok(ctx) => {
            ctx
        }
        Err(e) => {
            println!("{}", e);
            return;
        }
    };

    loop {
        match ctx.stack.pop() {
            None => {
                return
            }
            Some(i) => {
                println!("{}", i)
            }
        }
    }
}



///////////////////////////////////////////////////////////////////////////////////
//
// tests
//
///////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use lexx::input::InputString;

    use crate::{collect_uml, make_parse_context, run_script};
    use crate::value::Value;

    #[test]
    fn test_basic_parse_and_execute() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("1"))));

        let ctx = run_script(&mut pc);

        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(1)));
    }

    #[test]
    fn test_basic_addition() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("1 + 2"))));

        let ctx = run_script(&mut pc);

        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(3)));
    }

    #[test]
    fn test_basic_precedence() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("1 + 2 * 3"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(7)));

        pc.lexx.set_input(Box::new(InputString::new(String::from("2 * 3 + 1"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(7)));
    }

    #[test]
    fn test_basic_sub() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("(1 + 2) * 3"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(9)));

        pc.lexx.set_input(Box::new(InputString::new(String::from("2 * (3 + 1)"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(8)));
    }

    #[test]
    fn test_basic_sub_sub() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("(6+((2 * (3 + 1))/2))"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(10)));

        pc.lexx.set_input(Box::new(InputString::new(String::from("((((3 + 1))))"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(4)));
    }

    #[test]
    fn test_prefix_negate() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("-1"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(-1)));

        pc.lexx.set_input(Box::new(InputString::new(String::from("3 * -5"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(-15)));

        pc.lexx.set_input(Box::new(InputString::new(String::from("-3 * -5"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(15)));

        pc.lexx.set_input(Box::new(InputString::new(String::from("-3 + -5"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(-8)));

        pc.lexx.set_input(Box::new(InputString::new(String::from("(6+(-(2 * (3 + 1))/-2))"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(10)));
    }

    #[test]
    fn test_ternary_branch() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("1 ? 1 : 0"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(1)));

        pc.lexx.set_input(Box::new(InputString::new(String::from("0 ? 1 : 0"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(0)));

        pc.lexx.set_input(Box::new(InputString::new(String::from("1 + (-1) ? (3 * 6 + 1) : (5 * 2) + 2"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(22)));

        pc.lexx.set_input(Box::new(InputString::new(String::from("(1 + -1) ? (3 * 6 + 1) : (5 * 2) + 2"))));
        let ctx = run_script(&mut pc);
        assert_eq!(ctx.unwrap().stack.pop(), Some(Value::Int(12)));
    }

    #[test]
    fn test_chaining_expressions() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("1+2 3 + 4 5+6 "))));
        let mut ctx = run_script(&mut pc);
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(Value::Int(11)));
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(Value::Int(7)));
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(Value::Int(3)));

        pc.lexx.set_input(Box::new(InputString::new(String::from("(1+2); -(3 + 4) (5+6)"))));
        let mut ctx = run_script(&mut pc);
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(Value::Int(11)));
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(Value::Int(-7)));
        assert_eq!(ctx.as_mut().unwrap().stack.pop(), Some(Value::Int(3)));
    }

    #[test]
    fn test_expression_uml() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("2 + 3 * 4 - 5 * 9 / 3"))));
        let uml = collect_uml(&mut pc);
        println!("{}", uml.unwrap());
    }

    #[test]
    fn test_type_uml() {
        let mut pc = make_parse_context(Box::new(InputString::new(String::from("let test : number"))));
        let uml = collect_uml(&mut pc);
        println!("{}", uml.unwrap());
    }
}