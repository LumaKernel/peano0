use num_bigint::BigUint;
use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::convert::Infallible;
use std::str::FromStr;

pub struct ToLatexContext {
    id_to_latex: FxHashMap<LocalNameRef, String>,
    preferred_name: FxHashMap<LocalNameRef, Name>,
    name_use_count: FxHashMap<Name, usize>,
}
impl ToLatexContext {
    fn new() -> Self {
        ToLatexContext {
            id_to_latex: FxHashMap::default(),
            preferred_name: FxHashMap::default(),
            name_use_count: FxHashMap::default(),
        }
    }
    fn register_scope(&mut self, sf: &ScopedFormula) {
        self.preferred_name
            .insert(sf.local_name.id, sf.local_name.preferred_name.clone());
    }
    fn id_to_latex(&mut self, id: LocalNameRef) -> &String {
        self.id_to_latex.entry(id).or_insert_with(|| {
            let preferred_name = self
                .preferred_name
                .get(&id)
                .unwrap_or_else(|| panic!("No preferred name for {:?}", id));
            let index = self
                .name_use_count
                .entry(preferred_name.clone())
                .or_insert(0);
            *index += 1;
            format!("{}_{{{}}}", preferred_name.0, index)
        })
    }
}

pub trait ToLatex {
    fn to_latex(&self, ctx: &mut ToLatexContext) -> String;
}

pub fn to_latex(mut t: Formula) -> String {
    let mut ctx = ToLatexContext::new();
    t.roll_up();
    t.to_latex(&mut ctx)
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct Name(String);
impl FromStr for Name {
    type Err = Infallible;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Name(s.to_string()))
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
pub struct LocalNameRef(usize);

pub struct VarMaker(LocalNameRef);
impl VarMaker {
    pub fn var(&self) -> Term {
        Term::Var(self.0)
    }
}

#[derive(Clone, Debug)]
pub struct LocalName {
    preferred_name: Name,
    id: LocalNameRef,
}
impl LocalName {
    fn to_var_maker(&self) -> VarMaker {
        VarMaker(self.id)
    }
}

#[derive(Debug)]
pub struct ScopedFormula {
    local_name: LocalName,
    body: Box<Formula>,
}
impl Clone for ScopedFormula {
    fn clone(&self) -> Self {
        let old_id = self.local_name.id;
        let new_id = next_local_id();
        ScopedFormula {
            local_name: LocalName {
                preferred_name: self.local_name.preferred_name.clone(),
                id: new_id,
            },
            body: Box::new(self.body.clone().replace_var(old_id, Term::Var(new_id))),
        }
    }
}
impl ScopedFormula {
    fn replace_var(&self, replace_id: LocalNameRef, new_term: Term) -> ScopedFormula {
        ScopedFormula {
            local_name: self.local_name.clone(),
            body: Box::new(self.body.replace_var(replace_id, new_term)),
        }
    }
}

fn fast_union<T, S>(mut a: HashSet<T, S>, mut b: HashSet<T, S>) -> HashSet<T, S>
where
    T: Eq + std::hash::Hash,
    S: std::hash::BuildHasher + Default,
{
    if a.len() < b.len() {
        std::mem::swap(&mut a, &mut b);
    }
    a.extend(b);
    a
}

#[derive(Clone, Debug)]
pub enum Term {
    Nat(BigUint),
    Add(Box<Term>, Box<Term>),
    Mul(Box<Term>, Box<Term>),
    Var(LocalNameRef),
    GlobalVar(Name),

    // The value that's satisfying...
    Val(ScopedFormula),
}
impl Term {
    fn replace_var(&self, replace_id: LocalNameRef, new_term: Term) -> Term {
        match self {
            Term::Nat(n) => Term::Nat(n.clone()),
            Term::Add(a, b) => Term::Add(
                Box::new(a.replace_var(replace_id, new_term.clone())),
                Box::new(b.replace_var(replace_id, new_term)),
            ),
            Term::Mul(a, b) => Term::Mul(
                Box::new(a.replace_var(replace_id, new_term.clone())),
                Box::new(b.replace_var(replace_id, new_term)),
            ),
            Term::Var(id) => {
                if *id == replace_id {
                    new_term
                } else {
                    Term::Var(*id)
                }
            }
            Term::GlobalVar(name) => Term::GlobalVar(name.clone()),
            Term::Val(sf) => Term::Val(sf.replace_var(replace_id, new_term)),
        }
    }
    fn hoist_var(&mut self) -> Result<(), ScopedFormula> {
        let var = match self {
            Term::Add(a, b) => {
                a.hoist_var()?;
                b.hoist_var()?;
                return Ok(());
            }
            Term::Mul(a, b) => {
                a.hoist_var()?;
                b.hoist_var()?;
                return Ok(());
            }
            Term::Nat(..) | Term::Var(..) | Term::GlobalVar(..) => {
                return Ok(());
            }
            Term::Val(sf) => {
                //sf.body.hoist_var()?;
                Term::Var(sf.local_name.id)
            }
        };
        let val = std::mem::replace(self, var);
        Err(match val {
            Term::Val(sf) => sf,
            _ => unsafe { std::hint::unreachable_unchecked() },
        })
    }
}
impl ToLatex for Term {
    fn to_latex(&self, ctx: &mut ToLatexContext) -> String {
        match self {
            Term::Nat(n) => n.to_string(),
            Term::Add(a, b) => {
                let a_latex = a.to_latex(ctx);
                let mut b_latex = b.to_latex(ctx);
                if matches!(b.as_ref(), Term::Add(..)) {
                    b_latex = format!("({})", b_latex);
                }
                format!("{} + {}", a_latex, b_latex)
            }
            Term::Mul(a, b) => {
                let mut a_latex = a.to_latex(ctx);
                let mut b_latex = b.to_latex(ctx);
                if matches!(a.as_ref(), Term::Add(..)) {
                    a_latex = format!("({})", a_latex);
                }
                if matches!(b.as_ref(), Term::Add(..) | Term::Mul(..)) {
                    b_latex = format!("({})", b_latex);
                }
                format!("{} \\times {}", a_latex, b_latex)
            }
            Term::Var(id) => ctx
                .id_to_latex
                .entry(*id)
                .or_insert_with(|| {
                    let preferred_name = ctx
                        .preferred_name
                        .get(id)
                        .unwrap_or_else(|| panic!("No preferred name for {:?}", id));
                    let index = ctx
                        .name_use_count
                        .entry(preferred_name.clone())
                        .or_insert(0);
                    *index += 1;
                    format!("{}_{{{}}}", preferred_name.0, index)
                })
                .clone(),
            Term::GlobalVar(name) => format!("\\mathbf{{{}}}", name.0.clone()),
            Term::Val(..) => panic!("Val should not appear in the latex output"),
        }
    }
}

use once_cell::sync::Lazy;
use std::sync::Mutex;

static LOCAL_NEXT: Lazy<Mutex<usize>> = Lazy::new(|| Mutex::new(0));

pub fn next_local_id() -> LocalNameRef {
    let mut next = LOCAL_NEXT.lock().unwrap();
    let r = LocalNameRef(*next);
    *next += 1;
    r
}
fn local(s: &str) -> LocalName {
    LocalName {
        preferred_name: s.parse().unwrap(),
        id: next_local_id(),
    }
}

pub fn zero() -> Term {
    Term::Nat(BigUint::from(0_usize))
}
pub fn one() -> Term {
    Term::Nat(BigUint::from(1_usize))
}
pub fn two() -> Term {
    Term::Nat(BigUint::from(2_usize))
}
pub fn three() -> Term {
    Term::Nat(BigUint::from(3_usize))
}

pub fn eq(a: Term, b: Term) -> Formula {
    Formula::Eq(a, b)
}

pub fn add(a: Term, b: Term) -> Term {
    Term::Add(Box::new(a), Box::new(b))
}

pub fn mul(a: Term, b: Term) -> Term {
    Term::Mul(Box::new(a), Box::new(b))
}

//pub fn var(s: &str) -> Term {
//    Term::Var(s.parse().unwrap())
//}

pub fn and(a: Formula, b: Formula) -> Formula {
    Formula::And(Box::new(a), Box::new(b))
}

pub fn and_vec(v: Vec<Formula>) -> Formula {
    if v.is_empty() {
        bot()
    } else {
        let mut f = v[0].clone();
        for e in v.into_iter().skip(1) {
            f = and(f, e);
        }
        f
    }
}
#[macro_export]
macro_rules! and {
    ($($e:expr),* $(,)?) => {
        and_vec(vec![$($e),*])
    };
}

pub fn or(a: Formula, b: Formula) -> Formula {
    Formula::Or(Box::new(a), Box::new(b))
}
pub fn or_vec(v: Vec<Formula>) -> Formula {
    if v.is_empty() {
        bot()
    } else {
        let mut f = v[0].clone();
        for e in v.into_iter().skip(1) {
            f = or(f, e);
        }
        f
    }
}
#[macro_export]
macro_rules! or {
    ($($e:expr),* $(,)?) => {
        or_vec(vec![$($e),*])
    };
}

pub fn global_var(s: &str) -> Term {
    Term::GlobalVar(s.parse().unwrap())
}

pub fn not(a: Formula) -> Formula {
    Formula::Not(Box::new(a))
}

pub fn bot() -> Formula {
    Formula::Bot
}

pub fn implies(a: Formula, b: Formula) -> Formula {
    Formula::Implies(Box::new(a), Box::new(b))
}

pub fn all(s: &str, body: impl FnOnce(&VarMaker) -> Formula) -> Formula {
    let local_name = local(s);
    let var_maker = local_name.to_var_maker();
    let body = Box::new(body(&var_maker));
    Formula::Forall(ScopedFormula { local_name, body })
}

pub fn ex(s: &str, body: impl FnOnce(&VarMaker) -> Formula) -> Formula {
    let local_name = local(s);
    let var_maker = local_name.to_var_maker();
    let body = Box::new(body(&var_maker));
    Formula::Exists(ScopedFormula { local_name, body })
}

pub fn val(s: &str, body: impl FnOnce(&VarMaker) -> Formula) -> Term {
    let local_name = local(s);
    let var_maker = local_name.to_var_maker();
    let body = Box::new(body(&var_maker));
    Term::Val(ScopedFormula { local_name, body })
}

pub fn add_vec(v: Vec<Term>) -> Term {
    if v.is_empty() {
        zero()
    } else {
        let mut t = v[0].clone();
        for e in v.into_iter().skip(1) {
            t = Term::Add(Box::new(t), Box::new(e));
        }
        t
    }
}
#[macro_export]
macro_rules! add {
    ($($e:expr),* $(,)?) => {
        add_vec(vec![$($e),*])
    };
}

pub fn mul_vec(v: Vec<Term>) -> Term {
    if v.is_empty() {
        one()
    } else {
        let mut t = v[0].clone();
        for e in v.into_iter().skip(1) {
            t = Term::Mul(Box::new(t), Box::new(e));
        }
        t
    }
}
#[macro_export]
macro_rules! mul {
    ($($e:expr),* $(,)?) => {
        mul_vec(vec![$($e),*])
    };
}

#[derive(Clone, Debug)]
pub enum Formula {
    Eq(Term, Term),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Not(Box<Formula>),
    Bot,
    Implies(Box<Formula>, Box<Formula>),
    Forall(ScopedFormula),
    Exists(ScopedFormula),
}
impl Formula {
    fn replace_var(&self, replace_id: LocalNameRef, new_term: Term) -> Formula {
        match self {
            Formula::Eq(a, b) => Formula::Eq(
                a.replace_var(replace_id, new_term.clone()),
                b.replace_var(replace_id, new_term),
            ),
            Formula::And(a, b) => Formula::And(
                Box::new(a.replace_var(replace_id, new_term.clone())),
                Box::new(b.replace_var(replace_id, new_term)),
            ),
            Formula::Or(a, b) => Formula::Or(
                Box::new(a.replace_var(replace_id, new_term.clone())),
                Box::new(b.replace_var(replace_id, new_term)),
            ),
            Formula::Not(a) => Formula::Not(Box::new(a.replace_var(replace_id, new_term))),
            Formula::Bot => Formula::Bot,
            Formula::Implies(a, b) => Formula::Implies(
                Box::new(a.replace_var(replace_id, new_term.clone())),
                Box::new(b.replace_var(replace_id, new_term)),
            ),
            Formula::Forall(sf) => Formula::Forall(sf.replace_var(replace_id, new_term)),
            Formula::Exists(sf) => Formula::Exists(sf.replace_var(replace_id, new_term)),
        }
    }
    fn hoist_var(&mut self) -> Result<(), ScopedFormula> {
        match self {
            Formula::Eq(a, b) => {
                a.hoist_var()?;
                b.hoist_var()?;
            }
            Formula::And(a, b) => {
                a.hoist_var()?;
                b.hoist_var()?;
            }
            Formula::Or(a, b) => {
                a.hoist_var()?;
                b.hoist_var()?;
            }
            Formula::Not(a) => a.hoist_var()?,
            Formula::Bot => {}
            Formula::Implies(a, b) => {
                a.hoist_var()?;
                b.hoist_var()?;
            }
            Formula::Forall(sf) => sf.body.hoist_var()?,
            Formula::Exists(sf) => sf.body.hoist_var()?,
        }
        Ok(())
    }
    fn roll_up(&mut self) {
        let mut sfs = vec![];
        match self {
            Formula::Eq(a, b) => {
                while let Err(sf) = a.hoist_var() {
                    sfs.push(sf);
                }
                while let Err(sf) = b.hoist_var() {
                    sfs.push(sf);
                }
            }
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                a.roll_up();
                b.roll_up();
                return;
            }
            Formula::Not(a) => {
                a.roll_up();
                return;
            }
            Formula::Bot => {
                return;
            }
            Formula::Forall(sf) | Formula::Exists(sf) => {
                sf.body.roll_up();
                return;
            }
        }
        if sfs.is_empty() {
            return;
        }
        let mut t = std::mem::replace(self, Formula::Bot);
        for sf in sfs {
            t = Formula::Forall(ScopedFormula {
                local_name: sf.local_name,
                body: Box::new(Formula::Implies(Box::new(*sf.body), Box::new(t))),
            });
        }
        *self = t;
        self.roll_up();
    }
}
impl ToLatex for Formula {
    fn to_latex(&self, ctx: &mut ToLatexContext) -> String {
        match self {
            Formula::Eq(a, b) => format!("{} = {}", a.to_latex(ctx), b.to_latex(ctx)),
            Formula::And(a, b) => {
                let mut a_latex = a.to_latex(ctx);
                let mut b_latex = b.to_latex(ctx);
                if !matches!(a.as_ref(), Formula::And(..)) {
                    a_latex = format!("({})", a_latex);
                }
                if !matches!(b.as_ref(), Formula::And(..)) {
                    b_latex = format!("({})", b_latex);
                }
                format!("{} \\wedge {}", a_latex, b_latex)
            }
            Formula::Or(a, b) => {
                let mut a_latex = a.to_latex(ctx);
                let mut b_latex = b.to_latex(ctx);
                if !matches!(a.as_ref(), Formula::Or(..)) {
                    a_latex = format!("({})", a_latex);
                }
                if !matches!(b.as_ref(), Formula::Or(..)) {
                    b_latex = format!("({})", b_latex);
                }
                format!("{} \\vee {}", a_latex, b_latex)
            }
            Formula::Not(a) => {
                let mut a_latex = a.to_latex(ctx);
                if !matches!(a.as_ref(), Formula::Forall(..) | Formula::Exists(..)) {
                    a_latex = format!("({})", a_latex);
                }
                format!("\\neg {}", a_latex)
            }
            Formula::Bot => "\\bot".to_string(),
            Formula::Implies(a, b) => {
                format!("({}) \\rightarrow ({})", a.to_latex(ctx), b.to_latex(ctx))
            }
            Formula::Forall(sf) => {
                ctx.register_scope(sf);
                let mut body = sf.body.to_latex(ctx);
                let name = ctx.id_to_latex(sf.local_name.id);
                if !matches!(
                    *sf.body,
                    Formula::Forall(..) | Formula::Exists(..) | Formula::Eq(..)
                ) {
                    body = format!("({})", body);
                }
                format!("\\forall {} . {}", name, body)
            }
            Formula::Exists(sf) => {
                ctx.register_scope(sf);
                let mut body = sf.body.to_latex(ctx);
                let name = ctx.id_to_latex(sf.local_name.id);
                if !matches!(
                    *sf.body,
                    Formula::Forall(..) | Formula::Exists(..) | Formula::Eq(..)
                ) {
                    body = format!("({})", body);
                }
                format!("\\exists {} . {}", name, body)
            }
        }
    }
}
