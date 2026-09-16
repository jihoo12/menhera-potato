//! Batch 3: final pre-cubical audit.
//!
//! This file intentionally exercises the remaining boundary conditions before
//! the rollback kernel is treated as the baseline for adding an interval type.
//! No kernel implementation changes belong in this batch.

use std::panic::{AssertUnwindSafe, catch_unwind};

use rock::nbe::{self, Store};
use rock::{ConstructorDef, Ctx, Term, TermId, check, infer, nat_def, nat_suc, nat_zero, type0};

fn probe<T: std::fmt::Debug>(f: impl FnOnce() -> T) -> Result<T, String> {
    catch_unwind(AssertUnwindSafe(f)).map_err(|p| {
        p.downcast_ref::<String>()
            .cloned()
            .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_else(|| "non-string panic".into())
    })
}

fn reject_without_panic(store: &mut Store, tm: TermId) {
    let result = probe(|| infer(store, Ctx::empty(), tm));
    assert!(
        matches!(result, Ok(Err(_))),
        "expected TypeError, not acceptance or panic: {result:?}"
    );
}

fn con(store: &mut Store, def: TermId, idx: usize, args: Vec<TermId>) -> TermId {
    store.terms.alloc(Term::Con {
        def,
        idx,
        args,
        indices: vec![],
    })
}

fn bool_def(store: &mut Store) -> TermId {
    let l0 = store.levels.alloc(rock::Level::Zero);
    store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![
            ConstructorDef {
                name: "true".into(),
                arg_types: vec![],
                recursive: vec![],
                indices: vec![],
            },
            ConstructorDef {
                name: "false".into(),
                arg_types: vec![],
                recursive: vec![],
                indices: vec![],
            },
        ],
    })
}

fn numeral(store: &mut Store, nat: TermId, n: u32) -> TermId {
    let mut tm = nat_zero(store, nat);
    for _ in 0..n {
        tm = nat_suc(store, nat, tm);
    }
    tm
}

fn assert_nat_nf(store: &mut Store, nat: TermId, tm: TermId, expected: u32) {
    let nf = nbe::normalize(store, tm);
    let mut cur = nf;
    let mut n = 0;
    loop {
        match store.terms.get(cur) {
            Term::Con { def, idx: 0, args, .. } if *def == nat && args.is_empty() => break,
            Term::Con { def, idx: 1, args, .. } if *def == nat && args.len() == 1 => {
                n += 1;
                cur = args[0];
            }
            other => panic!("expected canonical Nat, got {other:?}"),
        }
    }
    assert_eq!(n, expected);
}

// -----------------------------------------------------------------------------
// A. Open terms / closure capture / substitution discipline
// -----------------------------------------------------------------------------

#[test]
fn batch3_open_beta_preserves_outer_capture() {
    let mut store = Store::new();

    // Under one outer binder y, evaluate (λx. y) Type0.
    // Inside the lambda body, y is Var(1).
    let captured = nbe::fresh_var(&mut store, 0);
    let env = store.envs.alloc(rock::Env {
        parent: None,
        value: captured,
    });

    let body = store.terms.alloc(Term::Var(1));
    let lam = store.terms.alloc(Term::Lam(body));
    let arg = type0(&mut store);
    let app = store.terms.alloc(Term::App(lam, arg));

    let got = nbe::eval(&mut store, Some(env), app);
    assert!(
        nbe::conv(&mut store, 1, got, captured),
        "beta reduction changed the captured outer variable"
    );
}

#[test]
fn batch3_nested_lambdas_preserve_outer_capture() {
    let mut store = Store::new();

    // Under y, λx. λz. y has body Var(2).
    let captured = nbe::fresh_var(&mut store, 0);
    let env = store.envs.alloc(rock::Env {
        parent: None,
        value: captured,
    });

    let body = store.terms.alloc(Term::Var(2));
    let inner = store.terms.alloc(Term::Lam(body));
    let outer = store.terms.alloc(Term::Lam(inner));
    let f = nbe::eval(&mut store, Some(env), outer);

    let a_tm = type0(&mut store);
    let a = nbe::eval(&mut store, Some(env), a_tm);
    let f1 = nbe::apply(&mut store, f, a);
    let b_tm = type0(&mut store);
    let b = nbe::eval(&mut store, Some(env), b_tm);
    let got = nbe::apply(&mut store, f1, b);

    assert!(nbe::conv(&mut store, 1, got, captured));
}

// -----------------------------------------------------------------------------
// B. De Bruijn scope across Π / Σ / Inductive
// -----------------------------------------------------------------------------

#[test]
fn batch3_open_pi_roundtrips_without_capture() {
    let mut store = Store::new();

    // A : Type0 |- Π (_ : A). A
    let u0 = type0(&mut store);
    let u0v = nbe::eval(&mut store, None, u0);
    let ctx = Ctx::empty().bind(&mut store, u0v);

    let a_dom = store.terms.alloc(Term::Var(0));
    let a_cod = store.terms.alloc(Term::Var(1));
    let pi = store.terms.alloc(Term::Pi(a_dom, a_cod));
    infer(&mut store, ctx, pi).expect("open Pi should be a type");

    let v = nbe::eval(&mut store, ctx.env, pi);
    let q = nbe::quote(&mut store, ctx.depth, v);
    let v2 = nbe::eval(&mut store, ctx.env, q);
    assert!(nbe::conv(&mut store, ctx.depth, v, v2));
}

#[test]
fn batch3_open_sigma_roundtrips_without_capture() {
    let mut store = Store::new();

    // A : Type0 |- Σ (_ : A). A
    let u0 = type0(&mut store);
    let u0v = nbe::eval(&mut store, None, u0);
    let ctx = Ctx::empty().bind(&mut store, u0v);

    let a_dom = store.terms.alloc(Term::Var(0));
    let a_cod = store.terms.alloc(Term::Var(1));
    let sigma = store.terms.alloc(Term::Sigma(a_dom, a_cod));
    infer(&mut store, ctx, sigma).expect("open Sigma should be a type");

    let v = nbe::eval(&mut store, ctx.env, sigma);
    let q = nbe::quote(&mut store, ctx.depth, v);
    let v2 = nbe::eval(&mut store, ctx.env, q);
    assert!(nbe::conv(&mut store, ctx.depth, v, v2));
}

#[test]
fn batch3_inductive_body_sees_outer_lambda_binder_at_shifted_index() {
    let mut store = Store::new();

    // λ(A : Type0). data BoxA : Type0 where box : A -> BoxA
    // Inside constructor field 0: self = Var(0), outer A = Var(1).
    let l0 = store.levels.alloc(rock::Level::Zero);
    let outer_a = store.terms.alloc(Term::Var(1));
    let box_a = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "box".into(),
            arg_types: vec![outer_a],
            recursive: vec![false],
            indices: vec![],
        }],
    });
    let family = store.terms.alloc(Term::Lam(box_a));

    let dom = type0(&mut store);
    let cod = type0(&mut store);
    let family_ty = store.terms.alloc(Term::Pi(dom, cod));
    let family_ty_v = nbe::eval(&mut store, None, family_ty);

    check(&mut store, Ctx::empty(), family, family_ty_v)
        .expect("outer binder was captured incorrectly inside Inductive");
}

// -----------------------------------------------------------------------------
// C. quote(eval(t)) semantic roundtrips
// -----------------------------------------------------------------------------

#[test]
fn batch3_closed_inductive_value_roundtrips_through_quote() {
    let mut store = Store::new();
    let b = bool_def(&mut store);
    infer(&mut store, Ctx::empty(), b).unwrap();

    let v = nbe::eval(&mut store, None, b);
    let q = nbe::quote(&mut store, 0, v);
    let v2 = nbe::eval(&mut store, None, q);
    assert!(nbe::conv(&mut store, 0, v, v2));
}

#[test]
fn batch3_dependent_pair_roundtrips_through_quote() {
    let mut store = Store::new();

    // (Type0, λx. x) : Σ (A : Type1). A -> A
    let ty1 = rock::type_n(&mut store, 1);
    let v0 = store.terms.alloc(Term::Var(0));
    let v1 = store.terms.alloc(Term::Var(1));
    let a_to_a = store.terms.alloc(Term::Pi(v0, v1));
    let sigma = store.terms.alloc(Term::Sigma(ty1, a_to_a));
    let sigma_v = nbe::eval(&mut store, None, sigma);

    let a = type0(&mut store);
    let x = store.terms.alloc(Term::Var(0));
    let id = store.terms.alloc(Term::Lam(x));
    let pair = store.terms.alloc(Term::Pair(a, id));
    check(&mut store, Ctx::empty(), pair, sigma_v).unwrap();

    let v = nbe::eval(&mut store, None, pair);
    let q = nbe::quote(&mut store, 0, v);
    let v2 = nbe::eval(&mut store, None, q);
    assert!(nbe::conv(&mut store, 0, v, v2));
}

// -----------------------------------------------------------------------------
// D. Small closed eliminator computations
// -----------------------------------------------------------------------------

#[test]
fn batch3_nat_eliminator_computes_two() {
    let mut store = Store::new();
    let nat = nat_def(&mut store);
    let target = numeral(&mut store, nat, 2);

    let motive = store.terms.alloc(Term::Lam(nat));
    let zero_branch = nat_zero(&mut store, nat);

    // suc branch receives predecessor, then IH. Return suc IH.
    let ih = store.terms.alloc(Term::Var(0));
    let suc_ih = nat_suc(&mut store, nat, ih);
    let lam_ih = store.terms.alloc(Term::Lam(suc_ih));
    let suc_branch = store.terms.alloc(Term::Lam(lam_ih));

    let case = store.terms.alloc(Term::Case {
        target,
        motive,
        branches: vec![zero_branch, suc_branch],
    });

    infer(&mut store, Ctx::empty(), case).expect("Nat eliminator should typecheck");
    assert_nat_nf(&mut store, nat, case, 2);
}

fn tagged(store: &mut Store) -> (TermId, TermId) {
    // Tagged (A : Type0) : Bool -> Type0
    // tag : (b : Bool) -> A -> Tagged A b
    let bool_tm = bool_def(store);
    let l0 = store.levels.alloc(rock::Level::Zero);
    let universe = type0(store);
    let a = store.terms.alloc(Term::Var(1));
    let result_b = store.terms.alloc(Term::Var(1));
    let def = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![universe],
        indices: vec![bool_tm],
        constructors: vec![ConstructorDef {
            name: "tag".into(),
            arg_types: vec![bool_tm, a],
            recursive: vec![false, false],
            indices: vec![result_b],
        }],
    });
    (def, bool_tm)
}

fn tagged_type(store: &mut Store, def: TermId, a: TermId, b: TermId) -> TermId {
    let da = store.terms.alloc(Term::App(def, a));
    store.terms.alloc(Term::App(da, b))
}

fn assert_tagged_case_returns(store: &mut Store, bool_idx: usize, n: u32) {
    let (def, bool_tm) = tagged(store);
    infer(store, Ctx::empty(), def).unwrap();

    let nat = nat_def(store);
    let payload = numeral(store, nat, n);
    let b = con(store, bool_tm, bool_idx, vec![]);
    let ty = tagged_type(store, def, nat, b);
    let target = con(store, def, 0, vec![b, payload]);
    let target = store.terms.alloc(Term::Ann(target, ty));

    let motive = store.terms.alloc(Term::Lam(nat));
    // branch binders: b, payload. Return payload = Var(0).
    let payload_var = store.terms.alloc(Term::Var(0));
    let payload_lam = store.terms.alloc(Term::Lam(payload_var));
    let branch = store.terms.alloc(Term::Lam(payload_lam));
    let case = store.terms.alloc(Term::Case {
        target,
        motive,
        branches: vec![branch],
    });

    infer(store, Ctx::empty(), case).expect("indexed Case should typecheck");
    assert_nat_nf(store, nat, case, n);
}

#[test]
fn batch3_indexed_eliminator_true_index_closed() {
    let mut store = Store::new();
    assert_tagged_case_returns(&mut store, 0, 1);
}

#[test]
fn batch3_indexed_eliminator_false_index_closed() {
    let mut store = Store::new();
    assert_tagged_case_returns(&mut store, 1, 3);
}

// -----------------------------------------------------------------------------
// E. Checked API malformed-input no-panic smoke tests
// -----------------------------------------------------------------------------

#[test]
fn batch3_unbound_variable_is_type_error_not_panic() {
    let mut store = Store::new();
    let dangling = store.terms.alloc(Term::Var(0));
    reject_without_panic(&mut store, dangling);
}

#[test]
fn batch3_constructor_wrong_arity_is_type_error_not_panic() {
    let mut store = Store::new();
    let b = bool_def(&mut store);
    infer(&mut store, Ctx::empty(), b).unwrap();
    let junk = type0(&mut store);
    let malformed = con(&mut store, b, 0, vec![junk]);
    reject_without_panic(&mut store, malformed);
}

#[test]
fn batch3_case_wrong_branch_count_is_type_error_not_panic() {
    let mut store = Store::new();
    let b = bool_def(&mut store);
    infer(&mut store, Ctx::empty(), b).unwrap();
    let target = con(&mut store, b, 0, vec![]);
    let motive_ty = type0(&mut store);
    let motive = store.terms.alloc(Term::Lam(motive_ty));
    let malformed = store.terms.alloc(Term::Case {
        target,
        motive,
        branches: vec![],
    });
    reject_without_panic(&mut store, malformed);
}

#[test]
fn batch3_missing_constructor_result_index_is_type_error_not_panic() {
    let mut store = Store::new();
    let bool_tm = bool_def(&mut store);
    let l0 = store.levels.alloc(rock::Level::Zero);
    let malformed = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![bool_tm],
        constructors: vec![ConstructorDef {
            name: "bad".into(),
            arg_types: vec![],
            recursive: vec![],
            indices: vec![],
        }],
    });
    reject_without_panic(&mut store, malformed);
}
