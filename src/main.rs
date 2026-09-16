//! Smoke demos for the rock MLTT kernel.

use rock::{
    Ctx, LevelBuilder, Store, Term, check, infer, nat_def, nat_suc, nat_zero, type_n, type_var,
    type0,
};

/// Build numeral n using a specific nat def.
fn nat_numeral(store: &mut Store, def: rock::TermId, n: u32) -> rock::TermId {
    let mut tm = nat_zero(store, def);
    for _ in 0..n {
        tm = nat_suc(store, def, tm);
    }
    tm
}

fn main() {
    println!("rock — MLTT kernel smoke checks\n");

    identity_demo();
    application_demo();
    universe_poly_demo();
    sigma_demo();
    nat_demo();
    ill_typed_demo();

    println!("all smoke checks passed.");
}

/// polymorphic identity: `λA. λx. x` at `(A : Type 1) → A → A`
fn identity_demo() {
    let mut store = Store::new();
    let ctx = Ctx::empty();

    let ty_a = type_n(&mut store, 1);
    let a_in_cod = store.terms.alloc(Term::Var(1));
    let a_in_dom = store.terms.alloc(Term::Var(0));
    let inner_pi = store.terms.alloc(Term::Pi(a_in_dom, a_in_cod));
    let id_ty = store.terms.alloc(Term::Pi(ty_a, inner_pi));

    let x = store.terms.alloc(Term::Var(0));
    let inner_lam = store.terms.alloc(Term::Lam(x));
    let id = store.terms.alloc(Term::Lam(inner_lam));

    let id_ty_val = rock::nbe::eval(&mut store, None, id_ty);
    check(&mut store, ctx, id, id_ty_val).expect("identity should typecheck");
    println!("✓ polymorphic identity : (A : Type1) → A → A");
}

/// `(id : (A:Type1)→A→A) Type0` has type `Type0 → Type0`;
/// under `x : Type0`, `(id Type0) x : Type0`.
fn application_demo() {
    let mut store = Store::new();

    let ty1 = type_n(&mut store, 1);
    let a_in_cod = store.terms.alloc(Term::Var(1));
    let a_in_dom = store.terms.alloc(Term::Var(0));
    let inner_pi = store.terms.alloc(Term::Pi(a_in_dom, a_in_cod));
    let id_ty = store.terms.alloc(Term::Pi(ty1, inner_pi));

    let x = store.terms.alloc(Term::Var(0));
    let inner_lam = store.terms.alloc(Term::Lam(x));
    let id = store.terms.alloc(Term::Lam(inner_lam));
    let annotated = store.terms.alloc(Term::Ann(id, id_ty));

    let ty0 = type0(&mut store);
    let app1 = store.terms.alloc(Term::App(annotated, ty0));
    let inferred = infer(&mut store, Ctx::empty(), app1).expect("id Type0");
    let ty0a = type0(&mut store);
    let ty0b = type0(&mut store);
    let expected = store.terms.alloc(Term::Pi(ty0a, ty0b));
    let expected_val = rock::nbe::eval(&mut store, None, expected);
    assert!(rock::conv(&mut store, 0, inferred, expected_val));

    let ty0c = type0(&mut store);
    let ty0c_val = rock::nbe::eval(&mut store, None, ty0c);
    let ctx = Ctx::empty().bind(&mut store, ty0c_val);
    let xvar = store.terms.alloc(Term::Var(0));
    let app2 = store.terms.alloc(Term::App(app1, xvar));
    let ty0d = type0(&mut store);
    let ty0d_val = rock::nbe::eval(&mut store, ctx.env, ty0d);
    check(&mut store, ctx, app2, ty0d_val).expect("(id Type0) x");
    println!("✓ identity application : Type0 → Type0 and (id Type0) x : Type0");
}

/// `Type α : Type (suc α)` for a level variable α
fn universe_poly_demo() {
    let mut store = Store::new();
    let ctx = Ctx::empty();

    let (ty_a, _) = type_var(&mut store, 0);
    let inferred = infer(&mut store, ctx, ty_a).expect("Type α");
    let mut lb = LevelBuilder {
        levels: &mut store.levels,
    };
    let a = lb.var(0);
    let suc_a = lb.suc(a);
    let expected = store.values.alloc(rock::Value::Univ(suc_a));
    assert!(rock::conv(&mut store, 0, inferred, expected));
    println!("✓ universe polymorphism : Type α : Type (suc α)");
}

/// dependent pair demo: `Σ(A : Type 1). A → A` with `(Type 0, λx. x)`
fn sigma_demo() {
    let mut store = Store::new();

    let ty1 = type_n(&mut store, 1);
    let v0 = store.terms.alloc(Term::Var(0));
    let v1 = store.terms.alloc(Term::Var(1));
    let id_a = store.terms.alloc(Term::Pi(v0, v1));
    let sigma_ty = store.terms.alloc(Term::Sigma(ty1, id_a));
    let sigma_val = rock::nbe::eval(&mut store, None, sigma_ty);

    let fst_tm = type0(&mut store);
    let vx = store.terms.alloc(Term::Var(0));
    let snd_tm = store.terms.alloc(Term::Lam(vx));
    let pair_tm = store.terms.alloc(Term::Pair(fst_tm, snd_tm));

    check(&mut store, Ctx::empty(), pair_tm, sigma_val)
        .expect("pair should typecheck against Sigma");

    let ctx = Ctx::empty().bind(&mut store, sigma_val);
    let p = store.terms.alloc(Term::Var(0));
    let fst_p = store.terms.alloc(Term::Fst(p));
    let snd_p = store.terms.alloc(Term::Snd(p));

    let fst_ty = infer(&mut store, ctx, fst_p).expect("fst p should infer");
    let exp_fst = rock::nbe::eval(&mut store, None, ty1);
    assert!(rock::nbe::conv(&mut store, ctx.depth, fst_ty, exp_fst));

    let snd_ty = infer(&mut store, ctx, snd_p).expect("snd p should infer");
    let p_in_dom = store.terms.alloc(Term::Var(0));
    let p_in_cod = store.terms.alloc(Term::Var(1));
    let exp_dom = store.terms.alloc(Term::Fst(p_in_dom));
    let exp_cod = store.terms.alloc(Term::Fst(p_in_cod));
    let exp_pi = store.terms.alloc(Term::Pi(exp_dom, exp_cod));
    let exp_snd = rock::nbe::eval(&mut store, ctx.env, exp_pi);
    assert!(rock::nbe::conv(&mut store, ctx.depth, snd_ty, exp_snd));

    let p_val = rock::nbe::fresh_var(&mut store, 0);
    let fst_v = rock::fst(&mut store, p_val);
    let snd_v = rock::snd(&mut store, p_val);
    let pair_v = store.values.alloc(rock::Value::Pair(fst_v, snd_v));
    assert!(rock::conv(&mut store, 1, pair_v, p_val));

    println!("✓ dependent sigma : (Type0, id) : Σ(A:Type1). A → A, projections, and η-equality");
}

/// Natural numbers inductive type demo: Nat, zero, suc, and addition via Case.
fn nat_demo() {
    let mut store = Store::new();
    let def = nat_def(&mut store);

    // Verify Nat : Type 0
    let nat_ty = infer(&mut store, Ctx::empty(), def).expect("Nat : Type 0");
    let ty0 = type0(&mut store);
    let ty0_val = rock::eval(&mut store, None, ty0);
    assert!(rock::conv(&mut store, 0, nat_ty, ty0_val));

    // add = λm. λn. case m { motive; branches: [n, λ_k. λih. suc ih] }
    let motive = store.terms.alloc(Term::Lam(def));
    let base_n = store.terms.alloc(Term::Var(0));
    let ih = store.terms.alloc(Term::Var(0));
    let suc_ih = nat_suc(&mut store, def, ih);
    let lam_ih = store.terms.alloc(Term::Lam(suc_ih));
    let step = store.terms.alloc(Term::Lam(lam_ih));
    let target_m = store.terms.alloc(Term::Var(1));

    let rec_add = store.terms.alloc(Term::Case {
        target: target_m,
        motive,
        branches: vec![base_n, step],
    });
    let lam_n = store.terms.alloc(Term::Lam(rec_add));
    let add = store.terms.alloc(Term::Lam(lam_n));

    let pi_inner = store.terms.alloc(Term::Pi(def, def));
    let add_ty = store.terms.alloc(Term::Pi(def, pi_inner));
    let add_ty_val = rock::eval(&mut store, None, add_ty);

    check(&mut store, Ctx::empty(), add, add_ty_val).expect("add : Nat → Nat → Nat");

    // Compute (add 2 3) = 5
    let ann_add = store.terms.alloc(Term::Ann(add, add_ty));
    let two = nat_numeral(&mut store, def, 2);
    let three = nat_numeral(&mut store, def, 3);
    let add_2 = store.terms.alloc(Term::App(ann_add, two));
    let add_2_3 = store.terms.alloc(Term::App(add_2, three));
    let nf = rock::normalize(&mut store, add_2_3);

    let mut curr = nf;
    let mut count = 0;
    loop {
        match *store.terms.get(curr) {
            Term::Con { idx: 0, .. } => break,
            Term::Con {
                idx: 1, ref args, ..
            } => {
                count += 1;
                curr = args[0];
            }
            ref other => panic!("expected numeral, got {other:?}"),
        }
    }
    assert_eq!(count, 5);
    println!("✓ inductive Nat : Nat, zero, suc, and (add 2 3) = 5 via Case");
}

fn ill_typed_demo() {
    let mut store = Store::new();
    let ctx = Ctx::empty();

    let tm = type0(&mut store);
    let ty = type0(&mut store);
    let ty_val = rock::nbe::eval(&mut store, None, ty);
    let err = check(&mut store, ctx, tm, ty_val);
    assert!(err.is_err(), "Type0 should not have type Type0");
    println!("✓ rejects Type0 : Type0");

    let mut store = Store::new();
    let tm = type0(&mut store);
    let ty2 = type_n(&mut store, 2);
    let ty2_val = rock::nbe::eval(&mut store, None, ty2);
    check(&mut store, Ctx::empty(), tm, ty2_val).expect("Type0 : Type2 via cumulativity");
    println!("✓ cumulativity : Type0 : Type2");
}
