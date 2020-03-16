fn main() {
    let id = direct::Expr::Fun(direct::Fun {
        arg: ":x".to_string(),
        body: Box::new(direct::Expr::Var(":x".to_string())),
    });
    let selfid: direct::Expr = direct::Expr::App(Box::new(id.clone()), Box::new(id));
    println!("Original:\n{}", selfid.to_sexp());
    println!(
        "Fischer:\n{:#?}",
        Fischer::new().convert_exp(selfid.clone()).to_sexp()
    );
    println!(
        "Dumb:\n{:#?}",
        Dumb::new().convert_exp(selfid.clone()).to_sexp()
    );
    println!(
        "Smart:\n{:#?}",
        Smart::new().convert_exp(selfid.clone()).to_sexp()
    )
}

use std::collections::HashMap;

/// Direct style syntax
mod direct {
    #[derive(Debug, Clone, PartialEq)]
    pub struct Fun {
        pub arg: String,
        pub body: Box<Expr>,
    }
    impl Fun {
        pub fn to_sexp(&self) -> sexp::Sexp {
            sexp::list(&[
                sexp::atom_s("fun"),
                sexp::atom_s(&self.arg),
                self.body.to_sexp(),
            ])
        }
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum Expr {
        Var(String),
        Fun(Fun),
        App(Box<Expr>, Box<Expr>),
        If(Box<Expr>, Box<Expr>, Box<Expr>),
    }

    impl Expr {
        pub fn to_sexp(&self) -> sexp::Sexp {
            match self {
                Expr::Var(s) => sexp::atom_s(&s),
                Expr::Fun(fun) => fun.to_sexp(),
                Expr::App(fun, arg) => sexp::list(&[fun.to_sexp(), arg.to_sexp()]),
                Expr::If(pred, then, els) => sexp::list(&[
                    sexp::atom_s("if"),
                    pred.to_sexp(),
                    then.to_sexp(),
                    els.to_sexp(),
                ]),
            }
        }
    }
}

/// CPS syntax
mod cps {
    #[derive(Debug, PartialEq)]
    pub enum Triv {
        Var(String),
        Lam {
            arg: String,
            cont: String,
            body: Box<Complex>,
        },
    }

    impl Triv {
        pub fn to_sexp(&self) -> sexp::Sexp {
            match self {
                Triv::Var(s) => sexp::atom_s(s),
                Triv::Lam { arg, cont, body } => sexp::list(&[
                    sexp::atom_s("lam"),
                    sexp::list(&[sexp::atom_s(arg), sexp::atom_s(cont)]),
                    body.to_sexp(),
                ]),
            }
        }
    }

    #[derive(Debug, PartialEq)]
    pub enum Cont {
        Var(String),
        Lam { arg: String, body: Box<Complex> },
        Halt,
    }

    impl Cont {
        pub fn to_sexp(&self) -> sexp::Sexp {
            match self {
                Cont::Var(x) => sexp::atom_s(x),
                Cont::Lam { arg, body } => {
                    sexp::list(&[sexp::atom_s("cont"), sexp::atom_s(arg), body.to_sexp()])
                }
                Cont::Halt => sexp::atom_s("halt"),
            }
        }
    }

    #[derive(Debug, PartialEq)]
    pub enum Complex {
        Call(Triv, Triv, Cont),
        Ret(Cont, Triv),
        If(Triv, Box<Complex>, Box<Complex>),
        LetC(String, Cont, Box<Complex>),
    }

    impl Complex {
        pub fn to_sexp(&self) -> sexp::Sexp {
            match self {
                Complex::Call(fun, arg, cont) => sexp::list(&[
                    sexp::atom_s("call"),
                    fun.to_sexp(),
                    arg.to_sexp(),
                    cont.to_sexp(),
                ]),

                Complex::Ret(cont, val) => {
                    sexp::list(&[sexp::atom_s("ret"), cont.to_sexp(), val.to_sexp()])
                }
                Complex::If(pred, then, els) => sexp::list(&[
                    sexp::atom_s("if"),
                    pred.to_sexp(),
                    then.to_sexp(),
                    els.to_sexp(),
                ]),
                Complex::LetC(v, cont, body) => sexp::list(&[
                    sexp::atom_s("letc"),
                    sexp::atom_s(v),
                    cont.to_sexp(),
                    body.to_sexp(),
                ]),
            }
        }
    }
}

/// The Fisher/Reynolds algorithm
struct Fischer {
    supply: u32,
}

impl Fischer {
    fn new() -> Fischer {
        Fischer { supply: 0 }
    }

    fn fresh(&mut self, s: &str) -> String {
        self.supply += 1;
        format!("{}{}", s, self.supply)
    }

    pub fn convert_exp(&mut self, expr: direct::Expr) -> cps::Complex {
        self.fischer(expr, cps::Cont::Halt)
    }

    fn fischer(&mut self, expr: direct::Expr, cont: cps::Cont) -> cps::Complex {
        match expr {
            direct::Expr::Var(x) => cps::Complex::Ret(cont, cps::Triv::Var(x)),
            direct::Expr::Fun(fun) => {
                let k = self.fresh("k");
                cps::Complex::Ret(
                    cont,
                    cps::Triv::Lam {
                        arg: fun.arg,
                        cont: k.clone(),
                        body: Box::new(self.fischer(*fun.body, cps::Cont::Var(k))),
                    },
                )
            }
            direct::Expr::App(fun, arg) => {
                let xf = self.fresh("xf");
                let xa = self.fresh("xa");
                let new_cont = self.fischer(
                    *arg,
                    cps::Cont::Lam {
                        arg: xa.clone(),
                        body: Box::new(cps::Complex::Call(
                            cps::Triv::Var(xf.clone()),
                            cps::Triv::Var(xa),
                            cont,
                        )),
                    },
                );
                self.fischer(
                    *fun,
                    cps::Cont::Lam {
                        arg: xf,
                        body: Box::new(new_cont),
                    },
                )
            }
            direct::Expr::If(p, t, e) => {
                let j = self.fresh("j");
                let xb = self.fresh("xb");
                let then = self.fischer(*t, cps::Cont::Var(j.clone()));
                let els = self.fischer(*e, cps::Cont::Var(j.clone()));
                self.fischer(
                    *p,
                    cps::Cont::Lam {
                        arg: xb.clone(),
                        body: Box::new(cps::Complex::LetC(
                            j,
                            cont,
                            Box::new(cps::Complex::If(
                                cps::Triv::Var(xb),
                                Box::new(then),
                                Box::new(els),
                            )),
                        )),
                    },
                )
            }
        }
    }
}

/// Abstract continuations and arguments
mod abs {
    use super::direct;
    use std::collections::HashMap;

    #[derive(Debug, Clone, PartialEq)]
    pub enum Cont {
        Halt,
        Var(String),
        Func(direct::Expr, Env, Box<Cont>),
        Arg(Arg, Box<Cont>),
        If(direct::Expr, direct::Expr, Env, Box<Cont>),
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum Arg {
        Var(String),
        StaticClosure {
            arg: String,
            body: direct::Expr,
            env: Env,
        },
    }

    pub type Env = HashMap<String, Arg>;
}

use abs::Env;

struct Dumb {
    supply: u32,
}

impl Dumb {
    fn new() -> Dumb {
        Dumb { supply: 0 }
    }

    fn fresh(&mut self, s: &str) -> String {
        self.supply += 1;
        format!("{}{}", s, self.supply)
    }

    pub fn convert_exp(&mut self, expr: direct::Expr) -> cps::Complex {
        self.convert(expr, std::collections::HashMap::new(), abs::Cont::Halt)
    }

    fn convert(&mut self, expr: direct::Expr, env: Env, cont: abs::Cont) -> cps::Complex {
        match expr {
            direct::Expr::Var(x) => self.ret(cont, env.get(&x).unwrap().clone()),
            direct::Expr::Fun(fun) => self.ret(
                cont,
                abs::Arg::StaticClosure {
                    arg: fun.arg,
                    body: *fun.body,
                    env,
                },
            ),
            direct::Expr::App(fun, arg) => self.convert(
                *fun,
                env.clone(),
                abs::Cont::Func(*arg, env, Box::new(cont)),
            ),
            direct::Expr::If(pred, then, els) => self.convert(
                *pred,
                env.clone(),
                abs::Cont::If(*then, *els, env, Box::new(cont)),
            ),
        }
    }

    fn ret(&mut self, cont: abs::Cont, arg: abs::Arg) -> cps::Complex {
        cps::Complex::Ret(self.bless_cont(cont), self.bless_arg(arg))
    }

    fn call(&mut self, func: abs::Arg, arg: abs::Arg, cont: abs::Cont) -> cps::Complex {
        cps::Complex::Call(
            self.bless_arg(func),
            self.bless_arg(arg),
            self.bless_cont(cont),
        )
    }

    fn r#if(
        &mut self,
        pred: abs::Arg,
        then: direct::Expr,
        els: direct::Expr,
        env: Env,
        cont: abs::Cont,
    ) -> cps::Complex {
        let j = self.fresh("j");
        cps::Complex::LetC(
            j.clone(),
            self.bless_cont(cont),
            Box::new(cps::Complex::If(
                self.bless_arg(pred),
                Box::new(self.convert(then, env.clone(), abs::Cont::Var(j.clone()))),
                Box::new(self.convert(els, env, abs::Cont::Var(j))),
            )),
        )
    }

    fn bless_cont(&mut self, cont: abs::Cont) -> cps::Cont {
        match cont {
            abs::Cont::Halt => cps::Cont::Halt,
            abs::Cont::Var(c) => cps::Cont::Var(c),
            abs::Cont::Func(e, env, cont) => {
                let xf = self.fresh("k");
                cps::Cont::Lam {
                    arg: xf.clone(),
                    body: Box::new(self.convert(e, env, abs::Cont::Arg(abs::Arg::Var(xf), cont))),
                }
            }
            abs::Cont::Arg(a, cont) => {
                let xa = self.fresh("k");
                cps::Cont::Lam {
                    arg: xa.clone(),
                    body: Box::new(self.call(a, abs::Arg::Var(xa), *cont)),
                }
            }
            abs::Cont::If(then, els, env, cont) => {
                let x = self.fresh("k");
                cps::Cont::Lam {
                    arg: x.clone(),
                    body: Box::new(self.r#if(abs::Arg::Var(x), els, then, env, *cont)),
                }
            }
        }
    }

    fn bless_arg(&mut self, arg: abs::Arg) -> cps::Triv {
        match arg {
            abs::Arg::Var(a) => cps::Triv::Var(a),
            abs::Arg::StaticClosure { arg, body, mut env } => {
                let x = self.fresh(&arg);
                let k = self.fresh("k");
                let _ = env.insert(arg, abs::Arg::Var(x.clone()));
                cps::Triv::Lam {
                    arg: x,
                    cont: k.clone(),
                    body: Box::new(self.convert(body, env, abs::Cont::Var(k))),
                }
            }
        }
    }
}

struct Smart {
    supply: u32,
    counts: HashMap<String, u32>,
}

impl Smart {
    fn new() -> Smart {
        Smart {
            supply: 0,
            counts: HashMap::new(),
        }
    }

    fn fresh(&mut self, s: &str) -> String {
        self.supply += 1;
        format!("{}{}", s, self.supply)
    }

    pub fn convert_exp(&mut self, expr: direct::Expr) -> cps::Complex {
        self.convert(expr, HashMap::new(), abs::Cont::Halt)
    }

    // TODO Actually implement the one_ref renamer
    fn one_ref(s: &str) -> bool {
        s.starts_with(":")
    }

    fn convert(&mut self, expr: direct::Expr, env: Env, cont: abs::Cont) -> cps::Complex {
        match expr {
            direct::Expr::Var(x) => self.ret(cont, env.get(&x).unwrap().clone()),
            direct::Expr::Fun(fun) => self.ret(
                cont,
                abs::Arg::StaticClosure {
                    arg: fun.arg,
                    body: *fun.body,
                    env,
                },
            ),
            direct::Expr::App(fun, arg) => self.convert(
                *fun,
                env.clone(),
                abs::Cont::Func(*arg, env, Box::new(cont)),
            ),
            direct::Expr::If(pred, then, els) => self.convert(
                *pred,
                env.clone(),
                abs::Cont::If(*then, *els, env, Box::new(cont)),
            ),
        }
    }

    fn ret(&mut self, cont: abs::Cont, arg: abs::Arg) -> cps::Complex {
        match cont {
            abs::Cont::Halt | abs::Cont::Var(_) => {
                cps::Complex::Ret(self.bless_cont(cont), self.bless_arg(arg))
            }
            abs::Cont::Func(e, env, c) => self.convert(e, env, abs::Cont::Arg(arg, c)),
            abs::Cont::Arg(a, c) => self.call(a, arg, *c),
            abs::Cont::If(e1, e2, env, c) => self.r#if(arg, e1, e2, env, *c),
        }
    }

    fn call(&mut self, func: abs::Arg, arg: abs::Arg, cont: abs::Cont) -> cps::Complex {
        let blessed_func = self.bless_arg(func.clone());
        match func {
            abs::Arg::Var(_) => {
                cps::Complex::Call(blessed_func, self.bless_arg(arg), self.bless_cont(cont))
            }
            abs::Arg::StaticClosure {
                arg: inner_arg,
                body,
                mut env,
            } => {
                if Self::one_ref(&inner_arg) {
                    env.insert(inner_arg, arg);
                    self.convert(body, env, cont)
                } else if let cps::Triv::Var(x) = blessed_func {
                    env.insert(inner_arg, abs::Arg::Var(x));
                    self.convert(body, env, cont)
                } else {
                    let x = self.fresh("x");
                    env.insert(inner_arg, abs::Arg::Var(x.clone()));
                    cps::Complex::Ret(
                        cps::Cont::Lam {
                            arg: x,
                            body: Box::new(self.convert(body, env, cont)),
                        },
                        blessed_func,
                    )
                }
            }
        }
    }

    fn r#if(
        &mut self,
        pred: abs::Arg,
        then: direct::Expr,
        els: direct::Expr,
        env: Env,
        cont: abs::Cont,
    ) -> cps::Complex {
        let j = self.fresh("j");
        cps::Complex::LetC(
            j.clone(),
            self.bless_cont(cont),
            Box::new(cps::Complex::If(
                self.bless_arg(pred),
                Box::new(self.convert(then, env.clone(), abs::Cont::Var(j.clone()))),
                Box::new(self.convert(els, env, abs::Cont::Var(j))),
            )),
        )
    }

    fn bless_cont(&mut self, cont: abs::Cont) -> cps::Cont {
        match cont {
            abs::Cont::Halt => cps::Cont::Halt,
            abs::Cont::Var(c) => cps::Cont::Var(c),
            _ => {
                let x = self.fresh("x");
                cps::Cont::Lam {
                    arg: x.clone(),
                    body: Box::new(self.ret(cont, abs::Arg::Var(x))),
                }
            }
        }
    }

    fn bless_arg(&mut self, arg: abs::Arg) -> cps::Triv {
        match arg {
            abs::Arg::Var(a) => cps::Triv::Var(a),
            abs::Arg::StaticClosure { arg, body, mut env } => {
                let x = self.fresh(&arg);
                let k = self.fresh("k");
                let _ = env.insert(arg, abs::Arg::Var(x.clone()));
                let converted_body = self.convert(body, env, abs::Cont::Var(k.clone()));
                match converted_body {
                    cps::Complex::Call(triv, arg, cont)
                        if self.counts.get(&x) == Some(&1)
                            && arg == cps::Triv::Var(x.clone())
                            && cont == cps::Cont::Var(k.clone()) =>
                    {
                        triv
                    }
                    _ => cps::Triv::Lam {
                        arg: x,
                        cont: k,
                        body: Box::new(converted_body),
                    },
                }
            }
        }
    }
}
