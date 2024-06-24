use anyhow::Result;
use indexmap::IndexSet;
use libra_types::{TypeIndex, TypeSet};
use smol_str::SmolStr;
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub enum Expr {
    Apply(Box<Expr>, Box<Expr>),
    Lambda(SmolStr, Box<Expr>),
    Let(SmolStr, Box<Expr>, Box<Expr>),
    Var(SmolStr),
    Int(u64),
}

impl Expr {
    pub fn apply(self, arg: Expr) -> Self {
        Expr::Apply(Box::new(self), Box::new(arg))
    }

    pub fn var(name: impl AsRef<str>) -> Self {
        Self::Var(SmolStr::new(name))
    }

    pub fn let_(name: impl AsRef<str>, binding: Expr, body: Expr) -> Self {
        Self::Let(SmolStr::new(name), Box::new(binding), Box::new(body))
    }

    pub fn lambda(name: impl AsRef<str>, body: Self) -> Self {
        Self::Lambda(SmolStr::new(name), Box::new(body))
    }

    pub fn int(int: u64) -> Self {
        Self::Int(int)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Label {
    Unify,
    Fun,
    Int,
}

pub struct Generate {
    types: TypeSet<Label>,
    locals: BTreeMap<SmolStr, TypeIndex>,
}

impl Generate {
    pub fn new() -> Self {
        Self {
            types: TypeSet::new(),
            locals: BTreeMap::new(),
        }
    }

    #[inline]
    pub fn insert_fun(
        &mut self,
        arg: Option<TypeIndex>,
        res: Option<TypeIndex>,
    ) -> (TypeIndex, [TypeIndex; 2]) {
        let (index, children) = self.types.insert_ctr(Label::Fun, 2);

        if let Some(arg) = arg {
            self.types.unify(children.get(0), arg).unwrap();
        }

        if let Some(res) = res {
            self.types.unify(children.get(1), res).unwrap();
        }

        (index, [children.get(0), children.get(1)])
    }

    #[inline]
    pub fn insert_int(&mut self) -> TypeIndex {
        let (index, _) = self.types.insert_ctr(Label::Int, 0);
        index
    }

    #[inline]
    pub fn insert_var(&mut self) -> TypeIndex {
        self.types.insert_var()
    }

    #[inline]
    pub fn unify(&mut self, a: TypeIndex, b: TypeIndex) -> TypeIndex {
        let (index, children) = self.types.insert_con(Label::Unify, 2);
        self.types.unify(children.get(0), a).unwrap();
        self.types.unify(children.get(1), b).unwrap();
        index
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

    #[inline]
    pub fn get_local(&self, name: &SmolStr) -> Option<TypeIndex> {
        self.locals.get(name).copied()
    }

    #[inline]
    pub fn finish(self) -> TypeSet<Label> {
        self.types
    }
}

pub fn generate_constraints(gen: &mut Generate, expr: &Expr) -> TypeIndex {
    match expr {
        Expr::Apply(f, arg) => {
            let f_t = generate_constraints(gen, f);
            let arg_t = generate_constraints(gen, arg);
            let (func, [_, func_res]) = gen.insert_fun(Some(arg_t), None);
            gen.unify(f_t, func);
            func_res
        }
        Expr::Lambda(var, body) => {
            let arg_t = gen.insert_var();
            let body_t = gen.with_local(var.clone(), arg_t, |gen| generate_constraints(gen, body));
            let (func, _) = gen.insert_fun(Some(arg_t), Some(body_t));
            func
        }
        Expr::Var(var) => gen.get_local(var).expect("unknown var"),
        Expr::Let(var, binding, body) => {
            let binding_t = generate_constraints(gen, binding);
            gen.with_local(var.clone(), binding_t, |gen| {
                generate_constraints(gen, body)
            })
        }
        Expr::Int(_) => gen.insert_int(),
    }
}

#[derive(Debug, Clone)]
pub struct TypeSchema {
    vars: usize,
    body: Type,
}

#[derive(Debug, Clone)]
pub enum Type {
    Var(usize),
    Fun(Box<Type>, Box<Type>),
    Int,
}

fn extract_type(
    solution: &TypeSet<Label>,
    vars: &mut IndexSet<TypeIndex>,
    index: TypeIndex,
) -> Option<Type> {
    match solution.get_type(index) {
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

pub fn extract_type_schema(solution: &TypeSet<Label>, index: TypeIndex) -> Option<TypeSchema> {
    let mut vars = IndexSet::new();
    let body = extract_type(solution, &mut vars, index)?;
    let vars = vars.len();
    Some(TypeSchema { vars, body })
}

pub fn main() -> Result<()> {
    // let expr = Expr::lambda(
    //     "f",
    //     Expr::lambda(
    //         "x",
    //         Expr::var("f").apply(Expr::var("f").apply(Expr::var("x"))),
    //     ),
    // );
    let expr = Expr::lambda(
        "f",
        Expr::lambda(
            "x",
            Expr::var("f").apply(Expr::var("f").apply(Expr::var("x"))),
        ),
    );

    let mut gen = Generate::new();
    let type_ix = generate_constraints(&mut gen, &expr);
    let mut types = gen.finish();

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

    // let (_, solution) = types.solve(|infer| {
    //     while let Some(index) = infer.pop_dirty() {
    //         if infer.is_disabled(index) {
    //             continue;
    //         }

    //         match infer.get_type(index) {
    //             TypeView::Const(name, cs) => match name {
    //                 Label::Unify => {
    //                     infer
    //                         .unify(cs.get(0), cs.get(1))
    //                         .map_err(|_| SolveError::new(index))?;
    //                     infer.mark_solved(index);
    //                 }
    //                 _ => {}
    //             },
    //             TypeView::Var(_) => {}
    //             TypeView::Type => {}
    //             TypeView::Constraint => {}
    //         }
    //     }

    //     Ok(type_ix)
    // });

    // println!("{:?}", solution.errors());
    println!("{:?}", extract_type_schema(&types, type_ix));

    Ok(())
}
