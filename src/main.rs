#![allow(dead_code)]
use peano0::*;

fn neq(a: Term, b: Term) -> Formula {
    // a != b  :=  not (a = b)
    Formula::Not(Box::new(Formula::Eq(a, b)))
}

fn le(a: Term, b: Term) -> Formula {
    // a <= b  :=  ex e. a + e = b
    ex("e", |e| eq(add(a, e.var()), b))
}
fn ge(a: Term, b: Term) -> Formula {
    // a >= b  :=  ex e. a = b + e
    ex("e", |e| eq(a, add(b, e.var())))
}
fn lt(a: Term, b: Term) -> Formula {
    // a < b  :=  ex e. a + e + 1 = b
    ex("e", |e| eq(add!(a, e.var(), one()), b))
}
fn gt(a: Term, b: Term) -> Formula {
    // a > b  :=  ex e. a = b + e + 1
    ex("e", |e| eq(a, add!(b, e.var(), one())))
}

fn r#mod(a: Term, b: Term) -> Term {
    // a % b = r  :=  ex d. a = b * d + r
    val("r", |r| ex("d", |d| eq(a, add(mul(b, d.var()), r.var()))))
}

fn div(a: Term, b: Term) -> Term {
    // a / b = d  :=  ex r. a = b * d + r
    val("d", |d| ex("r", |r| eq(a, add(mul(b, d.var()), r.var()))))
}

fn pred_min(pred: impl Fn(Term) -> Formula) -> Term {
    // pred_min(pred) = v  :=  pred(v) and all u. pred(u) implies u >= v
    val("v", |v| {
        and(
            pred(v.var()),
            all("u", |u| implies(pred(u.var()), ge(u.var(), v.var()))),
        )
    })
}

fn pred_max(pred: impl Fn(Term) -> Formula) -> Term {
    // pred_max(pred) = v  :=  pred(v) and all u. pred(u) implies u <= v
    val("v", |v| {
        and(
            pred(v.var()),
            all("u", |u| implies(pred(u.var()), le(u.var(), v.var()))),
        )
    })
}

fn pair_make(x: Term, y: Term) -> Term {
    // pair_make(x, y) = n  :=  2 * n = (x + y) * (x + y + 1) + 2 * y
    let x = move || x.clone();
    let y = move || y.clone();
    val("n", |n| {
        eq(
            mul(two(), n.var()),
            add(
                mul(add(x(), y()), add(add(x(), y()), one())),
                mul(two(), y()),
            ),
        )
    })
}

fn pair_get0(n: Term) -> Term {
    // pair_get0(n) = x  :=  ex y. n = pair_make(x, y)
    val("x", |x| ex("y", |y| eq(n, pair_make(x.var(), y.var()))))
}
fn pair_get1(n: Term) -> Term {
    // pair_get1(n) = y  :=  ex x. n = pair_make(x, y)
    val("y", |y| ex("x", |x| eq(n, pair_make(x.var(), y.var()))))
}

fn divides(a: Term, b: Term) -> Formula {
    // divides(a, b)  :=  ex d. a * d = b
    ex("d", |d| eq(mul(a, d.var()), b))
}

fn is_prime(n: Term) -> Formula {
    // is_prime(n)  :=  1 < n and all d. 1 < d and d < n implies not (d | n)
    let n = move || n.clone();
    and(
        gt(n(), one()),
        all("d", |d| {
            implies(
                and(lt(one(), d.var()), lt(d.var(), n())),
                not(divides(d.var(), n())),
            )
        }),
    )
}

fn is_pe(p: Term, v: Term) -> Formula {
    // ex e. p^e = v   :=  all q. is_prime q and p != q -> not (q | v)
    all("q", |q| {
        implies(
            and(is_prime(q.var()), neq(q.var(), p)),
            not(divides(q.var(), v)),
        )
    })
}

fn plist_first(p: Term, l: Term) -> Term {
    // a_0   :=   l % p
    r#mod(l, p)
}
fn plist_get_by_pe(p: Term, l: Term, pe: Term) -> Term {
    // assumes pe = p^e
    // a_e   :=   l / pe % p
    r#mod(div(l, pe), p)
}
fn plist_last(p: Term, l: Term) -> Term {
    // Assumes list has at least one non-zero element.
    // a_{-1}   :=  plist_get_by_pe( (min p^_ > l) / p )
    plist_get_by_pe(
        p.clone(),
        l.clone(),
        pred_min(|pe| and(is_pe(p.clone(), pe.clone()), gt(pe, l.clone()))),
    )
}

struct PlistPredContext {
    v0: Term,
    v1: Term,
}
impl PlistPredContext {
    fn v0(&self) -> Term {
        self.v0.clone()
    }
    fn v1(&self) -> Term {
        self.v1.clone()
    }
    fn x0(&self) -> Term {
        pair_get0(self.v0())
    }
    fn y0(&self) -> Term {
        pair_get1(self.v0())
    }
    fn x1(&self) -> Term {
        pair_get0(self.v1())
    }
    fn y1(&self) -> Term {
        pair_get1(self.v1())
    }
}
fn is_plist_with_pred(
    p: Term,
    l: Term,
    a0: Term,
    pred: impl FnOnce(PlistPredContext) -> Formula,
) -> Formula {
    and(
        // 初項
        eq(plist_first(p.clone(), l.clone()), a0),
        all("pe", |pe| {
            implies(
                and(
                    // peはp^e形である
                    is_pe(p.clone(), pe.var()),
                    // pe*pはl以下、つまりpeは最後より手前の要素に対応している
                    le(mul(pe.var(), p.clone()), l.clone()),
                ),
                {
                    let v0 = plist_get_by_pe(p.clone(), l.clone(), pe.var());
                    let v1 = plist_get_by_pe(p.clone(), l.clone(), mul(pe.var(), p.clone()));
                    let ctx = PlistPredContext { v0, v1 };
                    pred(ctx)
                },
            )
        }),
    )
}

// (i, a^i)
fn is_exp_plist(p: Term, l: Term, a: Term) -> Formula {
    is_plist_with_pred(
        p,
        l,
        // 初項 (0, 1)
        pair_make(zero(), one()),
        // (x', y') = (x+1, y*a)
        move |ctx| {
            and(
                eq(ctx.x1(), add(ctx.x0(), one())),
                eq(ctx.y1(), mul(ctx.y0(), a)),
            )
        },
    )
}

// a^k = b
fn a_pow_k_eq_b(a: Term, k: Term, b: Term) -> Formula {
    ex("l", |l| {
        ex("p", |p| {
            and!(
                is_prime(p.var()),
                is_exp_plist(p.var(), l.var(), a),
                eq(plist_last(p.var(), l.var()), pair_make(k, b)),
            )
        })
    })
}
fn a_pow_k(a: Term, k: Term) -> Term {
    val("b", |b| a_pow_k_eq_b(a, k, b.var()))
}

// (i, p_i)
fn is_prime_plist(p: Term, l: Term) -> Formula {
    is_plist_with_pred(
        p,
        l,
        // 初項 (0, 2)
        pair_make(zero(), two()),
        // (x', y') = (x+1, min is_prime and > y)
        move |ctx| {
            and(
                eq(ctx.x1(), add(ctx.x0(), one())),
                eq(
                    ctx.y1(),
                    pred_min(|v| and(is_prime(v.clone()), gt(v, ctx.y0()))),
                ),
            )
        },
    )
}

// i番目の素数
// p_i = p
fn is_ith_prime(i: Term, p: Term) -> Formula {
    let lhr = p;
    ex("l", |l| {
        ex("p", |p| {
            and!(
                is_prime_plist(p.var(), l.var()),
                eq(plist_last(p.var(), l.var()), pair_make(i, lhr)),
            )
        })
    })
}
fn ith_prime(i: Term) -> Term {
    val("p", |p| is_ith_prime(i, p.var()))
}

// フェルマーの最終定理
fn fermat_last_theorem() -> Formula {
    // n > 2 ならば、a^n + b^n = c^n は非自明な整数解を持たない
    all("n", |n| {
        implies(
            gt(n.var(), two()),
            all("a", |a| {
                all("b", |b| {
                    all("c", |c| {
                        not(eq(
                            add(a_pow_k(a.var(), n.var()), a_pow_k(b.var(), n.var())),
                            a_pow_k(c.var(), n.var()),
                        ))
                    })
                })
            }),
        )
    })
}

fn r#if(cond: Formula, then: Term, r#else: Term) -> Term {
    let cond = move || cond.clone();
    val("r", |r| {
        or(
            and(cond(), eq(r.var(), then)),
            and(not(cond()), eq(r.var(), r#else)),
        )
    })
}

// d'(0, n) = 0
// d'(i+1, n) = d'(i, n) + (i+1 | n ? i+1 : 0)
fn is_divisors0_plist(p: Term, l: Term, n: Term) -> Formula {
    is_plist_with_pred(
        p,
        l,
        // 初項 (0, 0)
        pair_make(zero(), n.clone()),
        // (x', y') = (x+1, y + (x+1 | n ? x+1 : 0))
        move |ctx| {
            and(
                eq(ctx.x1(), add(ctx.x0(), one())),
                eq(
                    ctx.y1(),
                    add(
                        ctx.y0(),
                        r#if(divides(ctx.x1(), n.clone()), ctx.x1(), zero()),
                    ),
                ),
            )
        },
    )
}
fn divisors(n: Term) -> Term {
    val("d", |d| {
        ex("l", |l| {
            ex("p", |p| {
                and(
                    is_divisors0_plist(p.var(), l.var(), n.clone()),
                    eq(plist_last(p.var(), l.var()), pair_make(n, d.var())),
                )
            })
        })
    })
}
// 完全数である
fn is_perfect(n: Term) -> Formula {
    // 2 * d(n) = n
    eq(mul(two(), divisors(n.clone())), n)
}
// 完全数は無限個存在
fn perfect_inf() -> Formula {
    all("n", |n| {
        ex("m", |m| and(is_perfect(m.var()), le(n.var(), m.var())))
    })
}

// 有理数は稠密である
// TODO

fn main() {
    // 2^k = m
    //let f1 = a_pow_k_eq_b(two(), global_var("k"), global_var("m"));
    let f1 = a_pow_k_eq_b(two(), global_var("k"), global_var("m"));
    //dbg!(&f1);
    //println!("{}", to_latex(f1));

    //let f2 = fermat_last_theorem();
    //println!("{}", to_latex(f2));

    println!("{}", to_latex(perfect_inf()));
}
