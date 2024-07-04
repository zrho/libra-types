use anyhow::Result;
use indexmap::IndexSet;
use libra_types::{TypeIndex, TypeSet};
use pest::iterators::Pair;
use pest::Parser;
use smol_str::SmolStr;
use std::collections::BTreeMap;
use std::str::FromStr;

// ANCHOR: expr
#[derive(Debug, Clone)]
pub enum Expr {
    Apply(Box<Expr>, Box<Expr>),
    Fun(SmolStr, Box<Expr>),
    Let(SmolStr, Box<Expr>, Box<Expr>),
    Var(SmolStr),
    Int(u64),
}
// ANCHOR_END: expr

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Label {
    Unify,
    Fun,
    Int,
}

pub struct Generate {
    locals: BTreeMap<SmolStr, TypeIndex>,
    types: TypeSet<Label>,
}

impl Generate {
    pub fn new() -> Self {
        Self {
            locals: BTreeMap::new(),
            types: TypeSet::new(),
        }
    }

    pub fn with_local<F, T>(&mut self, name: SmolStr, typ: TypeIndex, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let before = self.locals.insert(name.clone(), typ);
        let result = f(self);

        if let Some(before) = before {
            self.locals.insert(name, before);
        } else {
            self.locals.remove(&name);
        }

        result
    }

    pub fn get_local(&self, name: impl AsRef<str>) -> Option<TypeIndex> {
        self.locals.get(name.as_ref()).copied()
    }

    // ANCHOR: generate
    pub fn visit_expr(&mut self, expr: &Expr) -> TypeIndex {
        match expr {
            Expr::Apply(fun, arg) => self.visit_apply(fun, arg),
            Expr::Fun(var, body) => self.visit_fun(var, body),
            Expr::Let(var, binding, body) => self.visit_let(var, binding, body),
            Expr::Var(var) => self.visit_var(var),
            Expr::Int(_) => self.visit_int(),
        }
    }
    // ANCHOR_END: generate

    // ANCHOR: generate_apply
    fn visit_apply(&mut self, fun: &Expr, arg: &Expr) -> TypeIndex {
        let fun_t = self.visit_expr(fun);
        let arg_t = self.visit_expr(arg);

        let (arr, arr_args) = self.types.insert_ctr(Label::Fun, [Some(arg_t), None]);
        self.types
            .insert_con(Label::Unify, [Some(fun_t), Some(arr)]);

        arr_args.get(1)
    }
    // ANCHOR_END: generate_apply

    // ANCHOR: generate_fun
    fn visit_fun(&mut self, var: &SmolStr, body: &Expr) -> TypeIndex {
        let arg_t = self.types.insert_var();
        let body_t = self.with_local(var.clone(), arg_t, |ctx| ctx.visit_expr(body));
        let (arr, _) = self
            .types
            .insert_ctr(Label::Fun, [Some(arg_t), Some(body_t)]);
        arr
    }
    // ANCHOR_END: generate_fun

    // ANCHOR: generate_let
    fn visit_let(&mut self, var: &SmolStr, binding: &Expr, body: &Expr) -> TypeIndex {
        let binding_t = self.visit_expr(binding);
        self.with_local(var.clone(), binding_t, |ctx| ctx.visit_expr(body))
    }
    // ANCHOR_END: generate_let

    // ANCHOR: generate_var
    fn visit_var(&mut self, var: &str) -> TypeIndex {
        self.get_local(var).expect("unknown var")
    }
    // ANCHOR_END: generate_var

    // ANCHOR: generate_int
    fn visit_int(&mut self) -> TypeIndex {
        let (int_t, _) = self.types.insert_ctr(Label::Int, []);
        int_t
    }
    // ANCHOR_END: generate_int

    pub fn finish(self) -> TypeSet<Label> {
        self.types
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSchema {
    vars: usize,
    body: Type,
}

// ANCHOR: type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(usize),
    Fun(Box<Type>, Box<Type>),
    Int,
}
// ANCHOR_END: type

// ANCHOR: extract_type
fn extract_type(
    solution: &TypeSet<Label>,
    vars: &mut IndexSet<TypeIndex>,
    index: TypeIndex,
) -> Option<Type> {
    match solution.get(index) {
        libra_types::Type::Ctr(Label::Unify, _) => None,
        libra_types::Type::Ctr(Label::Fun, children) => {
            let arg = Box::new(extract_type(solution, vars, children.get(0))?);
            let res = Box::new(extract_type(solution, vars, children.get(1))?);
            Some(Type::Fun(arg, res))
        }
        libra_types::Type::Ctr(Label::Int, _) => Some(Type::Int),
        libra_types::Type::Var(var) => {
            let (var, _) = vars.insert_full(var);
            Some(Type::Var(var))
        }
        libra_types::Type::RowEmpty => None,
        libra_types::Type::RowCons(_) => None,
        libra_types::Type::Error => None,
    }
}
// ANCHOR_END: extract_type

// ANCHOR: extract_type_schema
pub fn extract_type_schema(solution: &TypeSet<Label>, index: TypeIndex) -> Option<TypeSchema> {
    let mut vars = IndexSet::new();
    let body = extract_type(solution, &mut vars, index)?;
    let vars = vars.len();
    Some(TypeSchema { vars, body })
}
// ANCHOR_END: extract_type_schema

pub fn infer_type(expr: &Expr) -> Result<TypeSchema> {
    let mut ctx = Generate::new();
    let type_ix = ctx.visit_expr(&expr);
    let mut types = ctx.finish();

    // ANCHOR: solve_loop
    while let Some((index, ctr, cs)) = types.pop_active() {
        match ctr {
            Label::Unify => {
                let a = cs.get(0);
                let b = cs.get(1);
                types.unify(a, b)?;
                types.mark_solved(index);
            }
            Label::Fun => {}
            Label::Int => {}
        }
    }
    // ANCHOR_END: solve_loop

    Ok(extract_type_schema(&types, type_ix).unwrap())
}

pub fn main() -> Result<()> {
    let example = r#"(fn (f x) (f x))"#;

    let expr: Expr = example.parse()?;
    let type_schema = infer_type(&expr)?;

    println!("{:?}", type_schema);

    Ok(())
}

mod parse {
    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "../examples/simple.pest"]
    pub struct SimpleParser;
}

impl FromStr for Expr {
    type Err = pest::error::Error<parse::Rule>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use parse::{Rule, SimpleParser};

        fn parse_expr_inner(pair: Pair<Rule>) -> Expr {
            match pair.as_rule() {
                Rule::expr => parse_expr_inner(pair.into_inner().next().unwrap()),
                Rule::expr_fun => {
                    let mut inner: Vec<_> = pair.into_inner().collect();
                    let mut expr = parse_expr_inner(inner.pop().unwrap());

                    while let Some(var) = inner.pop() {
                        expr = Expr::Fun(var.as_str().into(), Box::new(expr));
                    }

                    expr
                }
                Rule::expr_apply => {
                    let mut inner = pair.into_inner();
                    let mut expr = parse_expr_inner(inner.next().unwrap());

                    for arg in inner {
                        expr = Expr::Apply(Box::new(expr), Box::new(parse_expr_inner(arg)));
                    }

                    expr
                }
                Rule::expr_let => {
                    let mut inner = pair.into_inner();
                    let var = inner.next().unwrap().as_str();
                    let bind = parse_expr_inner(inner.next().unwrap());
                    let body = parse_expr_inner(inner.next().unwrap());
                    Expr::Let(var.into(), Box::new(bind), Box::new(body))
                }
                Rule::ident => Expr::Var(pair.as_span().as_str().into()),
                Rule::int => Expr::Int(pair.as_span().as_str().parse().unwrap()),
                r => unreachable!("{:?}", r),
            }
        }

        let pair = SimpleParser::parse(Rule::expr, s)?.next().unwrap();
        let expr = parse_expr_inner(pair);
        Ok(expr)
    }
}

impl FromStr for Type {
    type Err = pest::error::Error<parse::Rule>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use parse::{Rule, SimpleParser};

        fn parse_type_inner(pair: Pair<Rule>) -> Type {
            match pair.as_rule() {
                Rule::r#type => parse_type_inner(pair.into_inner().next().unwrap()),
                Rule::r#type_fun => {
                    let mut inner = pair.into_inner();
                    let arg = parse_type_inner(inner.next().unwrap());
                    let res = parse_type_inner(inner.next().unwrap());
                    Type::Fun(Box::new(arg), Box::new(res))
                }
                Rule::type_int => Type::Int,
                Rule::type_var => Type::Var(pair.as_span().as_str()[1..].parse().unwrap()),
                r => unreachable!("{:?}", r),
            }
        }

        let pair = SimpleParser::parse(Rule::r#type, s)?.next().unwrap();
        let typ = parse_type_inner(pair);
        Ok(typ)
    }
}

#[cfg(test)]
mod test {
    use super::{infer_type, Expr, Type};
    use rstest::rstest;

    #[rstest]
    #[case("(fn (f x) (f x))", "(-> (-> ?0 ?1) (-> ?0 ?1))")]
    #[case("(fn (f x) (f (f x)))", "(-> (-> ?0 ?0) (-> ?0 ?0))")]
    #[case("4", "int")]
    #[case("(fn (f) (f 1))", "(-> (-> int ?0) ?0)")]
    #[case("(let (x 1) x)", "int")]
    fn infer(#[case] program: &str, #[case] expected: &str) {
        let expected: Type = expected.parse().expect("parse type");
        let expr: Expr = program.parse().unwrap();
        let type_schema = infer_type(&expr).unwrap();
        assert_eq!(type_schema.body, expected);
    }

    #[test]
    fn detect_cycle() {
        let program = "(fn (f) (f f))";
        let expr = program.parse().unwrap();
        let result = infer_type(&expr);
        assert!(result.is_err());
    }
}
