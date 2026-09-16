//! Integration tests for the rock MLTT kernel.

use rock::level::LevelBuilder;
use rock::nbe::{self, Store};
use rock::term::{ConstructorDef, Term};
use rock::{
    Ctx, TypeError, check, infer, nat_def, nat_suc, nat_zero, normalize, type_n, type_var, type0,
};

/// Build numeral n using a specific nat def (so all terms share the same def).
fn nat_numeral(store: &mut Store, def: rock::TermId, n: u32) -> rock::TermId {
    let mut tm = nat_zero(store, def);
    for _ in 0..n {
        tm = nat_suc(store, def, tm);
    }
    tm
}

fn id_type(store: &mut Store) -> rock::TermId {
    // (A : Type1) → A → A  so we can instantiate A := Type0
    let ty_a = type_n(store, 1);
    let a_dom = store.terms.alloc(Term::Var(0));
    let a_cod = store.terms.alloc(Term::Var(1));
    let inner = store.terms.alloc(Term::Pi(a_dom, a_cod));
    store.terms.alloc(Term::Pi(ty_a, inner))
}

fn id_term(store: &mut Store) -> rock::TermId {
    let x = store.terms.alloc(Term::Var(0));
    let inner = store.terms.alloc(Term::Lam(x));
    store.terms.alloc(Term::Lam(inner))
}

#[test]
fn identity_typechecks() {
    let mut store = Store::new();
    let ty = id_type(&mut store);
    let tm = id_term(&mut store);
    let ty_val = nbe::eval(&mut store, None, ty);
    check(&mut store, Ctx::empty(), tm, ty_val).unwrap();
}

#[test]
fn identity_application() {
    let mut store = Store::new();
    let id_ty = id_type(&mut store);
    let id = id_term(&mut store);
    let annotated = store.terms.alloc(Term::Ann(id, id_ty));

    // id Type0  :  Type0 → Type0
    let ty0 = type0(&mut store);
    let app1 = store.terms.alloc(Term::App(annotated, ty0));
    let inferred = infer(&mut store, Ctx::empty(), app1).unwrap();
    let ty0a = type0(&mut store);
    let ty0b = type0(&mut store);
    let expected = store.terms.alloc(Term::Pi(ty0a, ty0b));
    let expected_val = nbe::eval(&mut store, None, expected);
    assert!(nbe::conv(&mut store, 0, inferred, expected_val));

    // under (x : Type0),  (id Type0) x  :  Type0
    let ty0c = type0(&mut store);
    let ty0c_val = nbe::eval(&mut store, None, ty0c);
    let ctx = Ctx::empty().bind(&mut store, ty0c_val);
    let x = store.terms.alloc(Term::Var(0));
    // app1 refers to Type0 at level 0; under one binder indices in app1 are unchanged
    // (closed term), so reuse app1.
    let app2 = store.terms.alloc(Term::App(app1, x));
    let ty0d = type0(&mut store);
    let ty0d_val = nbe::eval(&mut store, ctx.env, ty0d);
    check(&mut store, ctx, app2, ty0d_val).unwrap();
}

#[test]
fn nbe_beta_identity() {
    let mut store = Store::new();
    // (λx. x) applied is tested at value level: Lam(Var0) applied to Univ
    let x = store.terms.alloc(Term::Var(0));
    let lam = store.terms.alloc(Term::Lam(x));
    let ty0 = type0(&mut store);
    let app = store.terms.alloc(Term::App(lam, ty0));
    let nf = normalize(&mut store, app);
    match store.terms.get(nf) {
        Term::Univ(_) => {}
        other => panic!("expected Univ after NBE, got {other:?}"),
    }
}

#[test]
fn pi_infers_universe() {
    let mut store = Store::new();
    let ty0 = type0(&mut store);
    let a = store.terms.alloc(Term::Var(0));
    let pi = store.terms.alloc(Term::Pi(ty0, a));
    let inferred = infer(&mut store, Ctx::empty(), pi).unwrap();
    let ty1 = type_n(&mut store, 1);
    let ty1_val = nbe::eval(&mut store, None, ty1);
    assert!(nbe::conv(&mut store, 0, inferred, ty1_val));
}

#[test]
fn univ_typing() {
    let mut store = Store::new();
    let t0 = type0(&mut store);
    let inferred = infer(&mut store, Ctx::empty(), t0).unwrap();
    let t1 = type_n(&mut store, 1);
    let t1_val = nbe::eval(&mut store, None, t1);
    assert!(nbe::conv(&mut store, 0, inferred, t1_val));
}

#[test]
fn univ_poly() {
    let mut store = Store::new();
    let (ty_a, _) = type_var(&mut store, 0);
    let inferred = infer(&mut store, Ctx::empty(), ty_a).unwrap();
    let mut lb = LevelBuilder {
        levels: &mut store.levels,
    };
    let a = lb.var(0);
    let suc = lb.suc(a);
    let expected = store.values.alloc(rock::Value::Univ(suc));
    assert!(nbe::conv(&mut store, 0, inferred, expected));
}

#[test]
fn rejects_type0_as_type0() {
    let mut store = Store::new();
    let tm = type0(&mut store);
    let ty = type0(&mut store);
    let ty_val = nbe::eval(&mut store, None, ty);
    let err = check(&mut store, Ctx::empty(), tm, ty_val).unwrap_err();
    assert!(matches!(
        err,
        TypeError::ConversionFailure | TypeError::LevelMismatch
    ));
}

#[test]
fn cumulativity_type0_in_type2() {
    let mut store = Store::new();
    let tm = type0(&mut store);
    let ty2 = type_n(&mut store, 2);
    let ty2_val = nbe::eval(&mut store, None, ty2);
    check(&mut store, Ctx::empty(), tm, ty2_val).unwrap();
}

#[test]
fn lam_not_inferable() {
    let mut store = Store::new();
    let x = store.terms.alloc(Term::Var(0));
    let lam = store.terms.alloc(Term::Lam(x));
    let err = infer(&mut store, Ctx::empty(), lam).unwrap_err();
    assert_eq!(err, TypeError::ExpectedPi);
}

#[test]
fn eta_conversion() {
    let mut store = Store::new();
    let f = nbe::fresh_var(&mut store, 0);
    let v1 = store.terms.alloc(Term::Var(1));
    let v0 = store.terms.alloc(Term::Var(0));
    let app = store.terms.alloc(Term::App(v1, v0));
    let env = store.envs.alloc(rock::Env {
        parent: None,
        value: f,
    });
    let lam_val = store.values.alloc(rock::Value::Lam(rock::Closure {
        env: Some(env),
        body: app,
    }));
    assert!(nbe::conv(&mut store, 1, lam_val, f));
}

#[test]
fn sigma_formation_universe() {
    let mut store = Store::new();
    let ty0 = type0(&mut store);
    let a = store.terms.alloc(Term::Var(0));
    let sigma = store.terms.alloc(Term::Sigma(ty0, a));
    let inferred = infer(&mut store, Ctx::empty(), sigma).unwrap();
    let ty1 = type_n(&mut store, 1);
    let ty1_val = nbe::eval(&mut store, None, ty1);
    assert!(nbe::conv(&mut store, 0, inferred, ty1_val));

    let ty0_dom = type0(&mut store);
    let ty0_cod = type0(&mut store);
    let prod = store.terms.alloc(Term::Sigma(ty0_dom, ty0_cod));
    let inferred_prod = infer(&mut store, Ctx::empty(), prod).unwrap();
    assert!(nbe::conv(&mut store, 0, inferred_prod, ty1_val));
}

#[test]
fn pair_typechecks_dependent() {
    let mut store = Store::new();
    let ty1 = type_n(&mut store, 1);
    let v0 = store.terms.alloc(Term::Var(0));
    let v1 = store.terms.alloc(Term::Var(1));
    let id_a = store.terms.alloc(Term::Pi(v0, v1));
    let sigma_ty = store.terms.alloc(Term::Sigma(ty1, id_a));
    let sigma_val = nbe::eval(&mut store, None, sigma_ty);

    let fst_tm = type0(&mut store);
    let vx = store.terms.alloc(Term::Var(0));
    let snd_tm = store.terms.alloc(Term::Lam(vx));
    let pair_tm = store.terms.alloc(Term::Pair(fst_tm, snd_tm));

    check(&mut store, Ctx::empty(), pair_tm, sigma_val).unwrap();
}

#[test]
fn pair_projections_infer() {
    let mut store = Store::new();
    let ty1 = type_n(&mut store, 1);
    let v0 = store.terms.alloc(Term::Var(0));
    let v1 = store.terms.alloc(Term::Var(1));
    let id_a = store.terms.alloc(Term::Pi(v0, v1));
    let sigma_ty = store.terms.alloc(Term::Sigma(ty1, id_a));
    let sigma_val = nbe::eval(&mut store, None, sigma_ty);

    let ctx = Ctx::empty().bind(&mut store, sigma_val);
    let p = store.terms.alloc(Term::Var(0));
    let fst_p = store.terms.alloc(Term::Fst(p));
    let snd_p = store.terms.alloc(Term::Snd(p));

    let fst_ty = infer(&mut store, ctx, fst_p).unwrap();
    let expected_fst_ty = nbe::eval(&mut store, None, ty1);
    assert!(nbe::conv(&mut store, ctx.depth, fst_ty, expected_fst_ty));

    let snd_ty = infer(&mut store, ctx, snd_p).unwrap();
    let p_in_dom = store.terms.alloc(Term::Var(0));
    let p_in_cod = store.terms.alloc(Term::Var(1));
    let expected_dom = store.terms.alloc(Term::Fst(p_in_dom));
    let expected_cod = store.terms.alloc(Term::Fst(p_in_cod));
    let expected_pi = store.terms.alloc(Term::Pi(expected_dom, expected_cod));
    let expected_snd_ty = nbe::eval(&mut store, ctx.env, expected_pi);
    assert!(nbe::conv(&mut store, ctx.depth, snd_ty, expected_snd_ty));
}

#[test]
fn nbe_beta_sigma() {
    let mut store = Store::new();
    let ty0 = type0(&mut store);
    let ty1 = type_n(&mut store, 1);
    let pair = store.terms.alloc(Term::Pair(ty0, ty1));

    let fst_tm = store.terms.alloc(Term::Fst(pair));
    let snd_tm = store.terms.alloc(Term::Snd(pair));

    let nf_fst = normalize(&mut store, fst_tm);
    let nf_snd = normalize(&mut store, snd_tm);

    match store.terms.get(nf_fst) {
        Term::Univ(l) => {
            let l0 = store.levels.alloc(rock::Level::Zero);
            assert!(rock::eq_level(&store.levels, *l, l0));
        }
        other => panic!("expected Univ(0), got {other:?}"),
    }

    match store.terms.get(nf_snd) {
        Term::Univ(l) => {
            let mut lb = LevelBuilder {
                levels: &mut store.levels,
            };
            let l1 = lb.const_level(1);
            assert!(rock::eq_level(&store.levels, *l, l1));
        }
        other => panic!("expected Univ(1), got {other:?}"),
    }
}

#[test]
fn sigma_eta_conversion() {
    let mut store = Store::new();
    let p = nbe::fresh_var(&mut store, 0);
    let fst_val = nbe::fst(&mut store, p);
    let snd_val = nbe::snd(&mut store, p);
    let pair_val = store.values.alloc(rock::Value::Pair(fst_val, snd_val));

    assert!(nbe::conv(&mut store, 1, pair_val, p));
    assert!(nbe::conv(&mut store, 1, p, pair_val));
}

#[test]
fn sigma_type_errors() {
    let mut store = Store::new();
    let ty0 = type0(&mut store);
    let pair = store.terms.alloc(Term::Pair(ty0, ty0));

    let err = infer(&mut store, Ctx::empty(), pair).unwrap_err();
    assert_eq!(err, TypeError::ExpectedSigma);

    let fst_univ = store.terms.alloc(Term::Fst(ty0));
    let err_fst = infer(&mut store, Ctx::empty(), fst_univ).unwrap_err();
    assert_eq!(err_fst, TypeError::ExpectedSigma);

    let snd_univ = store.terms.alloc(Term::Snd(ty0));
    let err_snd = infer(&mut store, Ctx::empty(), snd_univ).unwrap_err();
    assert_eq!(err_snd, TypeError::ExpectedSigma);

    let ty0_val = nbe::eval(&mut store, None, ty0);
    let err_check = check(&mut store, Ctx::empty(), pair, ty0_val).unwrap_err();
    assert_eq!(err_check, TypeError::ExpectedSigma);
}

#[test]
fn nat_formation_and_constructors() {
    let mut store = Store::new();
    let def = nat_def(&mut store);

    // Nat : Type 0
    let ty = infer(&mut store, Ctx::empty(), def).unwrap();
    let ty0 = type0(&mut store);
    let ty0_val = nbe::eval(&mut store, None, ty0);
    assert!(nbe::conv(&mut store, 0, ty, ty0_val));

    // Nat : Type 1 via cumulativity
    let ty1 = type_n(&mut store, 1);
    let ty1_val = nbe::eval(&mut store, None, ty1);
    check(&mut store, Ctx::empty(), def, ty1_val).unwrap();

    // zero : Nat
    let z = nat_zero(&mut store, def);
    let nat_val = nbe::eval(&mut store, None, def);
    check(&mut store, Ctx::empty(), z, nat_val).unwrap();
    let z_ty = infer(&mut store, Ctx::empty(), z).unwrap();
    assert!(nbe::conv(&mut store, 0, z_ty, nat_val));

    // suc zero : Nat
    let sz = nat_suc(&mut store, def, z);
    check(&mut store, Ctx::empty(), sz, nat_val).unwrap();
    let sz_ty = infer(&mut store, Ctx::empty(), sz).unwrap();
    assert!(nbe::conv(&mut store, 0, sz_ty, nat_val));

    // suc (suc zero) : Nat
    let ssz = nat_suc(&mut store, def, sz);
    check(&mut store, Ctx::empty(), ssz, nat_val).unwrap();
}

#[test]
fn nat_rec_beta_zero() {
    let mut store = Store::new();
    let def = nat_def(&mut store);

    // Motive: λ_. Nat  (: Nat → Type 0)
    let motive = store.terms.alloc(Term::Lam(def));

    // Base case: zero (: Nat)
    let z = nat_zero(&mut store, def);

    // Step case: λn. λih. suc ih  (: (n : Nat) → Nat → Nat)
    let ih = store.terms.alloc(Term::Var(0));
    let s_body = nat_suc(&mut store, def, ih);
    let s_inner = store.terms.alloc(Term::Lam(s_body));
    let s = store.terms.alloc(Term::Lam(s_inner));

    // Case zero { motive; branches: [zero, suc] }
    let target = nat_zero(&mut store, def);
    let rec = store.terms.alloc(Term::Case {
        target,
        motive,
        branches: vec![z, s],
    });

    let nat_val = nbe::eval(&mut store, None, def);
    let rec_ty = infer(&mut store, Ctx::empty(), rec).unwrap();
    assert!(nbe::conv(&mut store, 0, rec_ty, nat_val));

    // Normalizes to zero
    let nf = normalize(&mut store, rec);
    match store.terms.get(nf) {
        Term::Con { idx: 0, .. } => {}
        other => panic!("expected zero (Con idx 0), got {other:?}"),
    }
}

fn assert_nat_numeral(store: &Store, mut tm: rock::TermId, expected: u32) {
    let mut count = 0;
    loop {
        match store.terms.get(tm) {
            Term::Con { idx: 0, .. } => break,
            Term::Con { idx: 1, args, .. } => {
                count += 1;
                tm = args[0];
            }
            other => panic!("expected numeral, got {other:?}"),
        }
    }
    assert_eq!(count, expected);
}

#[test]
fn nat_rec_beta_suc() {
    let mut store = Store::new();
    let def = nat_def(&mut store);

    // Motive: λ_. Nat
    let motive = store.terms.alloc(Term::Lam(def));

    // Base case: zero
    let z = nat_zero(&mut store, def);

    // Step case: λn. λih. suc ih
    let ih = store.terms.alloc(Term::Var(0));
    let s_body = nat_suc(&mut store, def, ih);
    let s_inner = store.terms.alloc(Term::Lam(s_body));
    let s = store.terms.alloc(Term::Lam(s_inner));

    // Target: 2 = suc (suc zero)
    let two = nat_numeral(&mut store, def, 2);
    let rec = store.terms.alloc(Term::Case {
        target: two,
        motive,
        branches: vec![z, s],
    });

    let nf = normalize(&mut store, rec);
    assert_nat_numeral(&store, nf, 2);
}

#[test]
fn nat_addition() {
    let mut store = Store::new();
    let def = nat_def(&mut store);

    // add m n = case m { motive; branches: [n, λ_k. λih. suc ih] }
    // Motive: λ_. Nat
    let motive = store.terms.alloc(Term::Lam(def));

    // Base: n (Var(0))
    let base_n = store.terms.alloc(Term::Var(0));

    // Step: λ_k. λih. suc ih
    let ih = store.terms.alloc(Term::Var(0));
    let suc_ih = nat_suc(&mut store, def, ih);
    let lam_ih = store.terms.alloc(Term::Lam(suc_ih));
    let step = store.terms.alloc(Term::Lam(lam_ih));

    // Target: m (Var(1))
    let target_m = store.terms.alloc(Term::Var(1));

    let rec_add = store.terms.alloc(Term::Case {
        target: target_m,
        motive,
        branches: vec![base_n, step],
    });

    // λn. rec_add
    let lam_n = store.terms.alloc(Term::Lam(rec_add));
    // λm. λn. rec_add
    let add = store.terms.alloc(Term::Lam(lam_n));

    // Type of add: Nat → Nat → Nat
    let pi_inner = store.terms.alloc(Term::Pi(def, def));
    let add_ty = store.terms.alloc(Term::Pi(def, pi_inner));
    let add_ty_val = nbe::eval(&mut store, None, add_ty);

    check(&mut store, Ctx::empty(), add, add_ty_val).unwrap();

    // Now test computation: (add 2 3) = 5
    let ann_add = store.terms.alloc(Term::Ann(add, add_ty));
    let two = nat_numeral(&mut store, def, 2);
    let three = nat_numeral(&mut store, def, 3);
    let add_2 = store.terms.alloc(Term::App(ann_add, two));
    let add_2_3 = store.terms.alloc(Term::App(add_2, three));

    let nf = normalize(&mut store, add_2_3);
    assert_nat_numeral(&store, nf, 5);

    // (add 0 n) ≅ n definitionally on closed terms
    let zero = nat_zero(&mut store, def);
    let four = nat_numeral(&mut store, def, 4);
    let add_0 = store.terms.alloc(Term::App(ann_add, zero));
    let add_0_4 = store.terms.alloc(Term::App(add_0, four));
    let nf_0_4 = normalize(&mut store, add_0_4);
    assert_nat_numeral(&store, nf_0_4, 4);
}

#[test]
fn nat_dependent_induction() {
    let mut store = Store::new();
    let def = nat_def(&mut store);

    // Dependent motive: P(n) = (n : Nat) → Type 0
    // Let P(n) = Pi(Nat, Nat) (a function type)
    // Base case: identity function λx. x
    // Step case: λn. λih. λx. suc (ih x)
    // Then rec(P, id, s, n) x computes n + x via higher-order dependent recursion.
    let pi_fn = store.terms.alloc(Term::Pi(def, def));
    let motive = store.terms.alloc(Term::Lam(pi_fn));

    // Base case: id = λx. x
    let vx = store.terms.alloc(Term::Var(0));
    let id_fn = store.terms.alloc(Term::Lam(vx));

    // Step case: λn. λih. λx. suc (ih x)
    // Binders: n (Var 2), ih (Var 1), x (Var 0)
    let vx0 = store.terms.alloc(Term::Var(0));
    let vih = store.terms.alloc(Term::Var(1));
    let app_ih_x = store.terms.alloc(Term::App(vih, vx0));
    let suc_app = nat_suc(&mut store, def, app_ih_x);
    let lam_x = store.terms.alloc(Term::Lam(suc_app));
    let lam_ih = store.terms.alloc(Term::Lam(lam_x));
    let step = store.terms.alloc(Term::Lam(lam_ih));

    let three = nat_numeral(&mut store, def, 3);
    let rec = store.terms.alloc(Term::Case {
        target: three,
        motive,
        branches: vec![id_fn, step],
    });

    let rec_ty = infer(&mut store, Ctx::empty(), rec).unwrap();
    let expected_ty_val = nbe::eval(&mut store, None, pi_fn);
    assert!(nbe::conv(&mut store, 0, rec_ty, expected_ty_val));

    // rec applied to 4 yields 3 + 4 = 7
    let four = nat_numeral(&mut store, def, 4);
    let app = store.terms.alloc(Term::App(rec, four));
    let nf = normalize(&mut store, app);
    assert_nat_numeral(&store, nf, 7);
}

#[test]
fn nat_neutral_elimination() {
    let mut store = Store::new();
    let def = nat_def(&mut store);
    let nat_val = nbe::eval(&mut store, None, def);

    // Context: (k : Nat)
    let ctx = Ctx::empty().bind(&mut store, nat_val);
    let k = store.terms.alloc(Term::Var(0));

    let motive = store.terms.alloc(Term::Lam(def));
    let z = nat_zero(&mut store, def);
    let ih = store.terms.alloc(Term::Var(0));
    let s_body = nat_suc(&mut store, def, ih);
    let s_inner = store.terms.alloc(Term::Lam(s_body));
    let s = store.terms.alloc(Term::Lam(s_inner));

    let rec = store.terms.alloc(Term::Case {
        target: k,
        motive,
        branches: vec![z, s],
    });

    // Inferred type is Nat under k : Nat
    let ty = infer(&mut store, ctx, rec).unwrap();
    assert!(nbe::conv(&mut store, ctx.depth, ty, nat_val));

    // Evaluating rec under ctx.env produces a stuck neutral
    let val = nbe::eval(&mut store, ctx.env, rec);
    match *store.values.get(val) {
        rock::Value::Neut(neut) => {
            assert_eq!(neut.level, 0);
            assert!(neut.spine.is_some());
        }
        ref other => panic!("expected neutral, got {other:?}"),
    }

    // Quoting preserves the Case stuck form
    let quoted = nbe::quote(&mut store, ctx.depth, val);
    match store.terms.get(quoted) {
        Term::Case { target, .. } => {
            assert!(matches!(store.terms.get(*target), Term::Var(0)));
        }
        other => panic!("expected Case term, got {other:?}"),
    }

    // Reflexivity of conv on neutral Case:
    assert!(nbe::conv(&mut store, ctx.depth, val, val));
}

#[test]
fn nat_canonicity() {
    // AGENTS.md §4: Closed Nat term normalizes to canonical numeral
    let mut store = Store::new();

    let def = nat_def(&mut store);
    let candidates = [
        nat_numeral(&mut store, def, 0),
        nat_numeral(&mut store, def, 1),
        nat_numeral(&mut store, def, 5),
    ];

    for tm in candidates {
        let nf = normalize(&mut store, tm);
        let mut curr = nf;
        loop {
            match store.terms.get(curr) {
                Term::Con { idx: 0, .. } => break,
                Term::Con { idx: 1, args, .. } => {
                    curr = args[0];
                }
                other => panic!("non-canonical normal form for closed Nat: {other:?}"),
            }
        }
    }
}

#[test]
fn nat_type_errors() {
    let mut store = Store::new();
    let ty0 = type0(&mut store);
    let def = nat_def(&mut store);

    // 1. suc applied to non-Nat (e.g. suc Type0)
    let bad1 = nat_suc(&mut store, def, ty0);
    let err = infer(&mut store, Ctx::empty(), bad1).unwrap_err();
    assert!(matches!(
        err,
        TypeError::ConversionFailure | TypeError::ExpectedInductive
    ));

    // 2. Motive not a function from Nat (e.g. Type0 -> Type0)
    let ty0_arr = store.terms.alloc(Term::Pi(ty0, ty0));
    let x = store.terms.alloc(Term::Var(0));
    let id_x = store.terms.alloc(Term::Lam(x));
    let bad_motive = store.terms.alloc(Term::Ann(id_x, ty0_arr));
    let z = nat_zero(&mut store, def);
    let lam_z = store.terms.alloc(Term::Lam(z));
    let s = store.terms.alloc(Term::Lam(lam_z));
    let bad_rec = store.terms.alloc(Term::Case {
        target: z,
        motive: bad_motive,
        branches: vec![z, s],
    });
    let err2 = infer(&mut store, Ctx::empty(), bad_rec).unwrap_err();
    assert!(matches!(
        err2,
        TypeError::ConversionFailure | TypeError::ExpectedInductive
    ));

    // 3. Base case type mismatch (expected Nat, got Type0)
    let motive = store.terms.alloc(Term::Lam(def));
    let bad_base_rec = store.terms.alloc(Term::Case {
        target: z,
        motive,
        branches: vec![ty0, s],
    });
    let err3 = infer(&mut store, Ctx::empty(), bad_base_rec).unwrap_err();
    assert_eq!(err3, TypeError::ConversionFailure);

    // 4. Target not a Nat (e.g. target is Type0)
    let motive4 = store.terms.alloc(Term::Lam(def));
    let bad_target_rec = store.terms.alloc(Term::Case {
        target: ty0,
        motive: motive4,
        branches: vec![z, s],
    });
    let err4 = infer(&mut store, Ctx::empty(), bad_target_rec).unwrap_err();
    assert!(matches!(
        err4,
        TypeError::ConversionFailure | TypeError::ExpectedInductive
    ));
}

// ===== General inductive type tests =====

fn bool_def(store: &mut Store) -> rock::TermId {
    let true_con = ConstructorDef {
        name: "true".to_string(),
        arg_types: vec![],
        recursive: vec![],
        indices: vec![],
    };
    let false_con = ConstructorDef {
        name: "false".to_string(),
        arg_types: vec![],
        recursive: vec![],
        indices: vec![],
    };
    store.terms.alloc(Term::Inductive {
        level: store.levels.alloc(rock::Level::Zero),
        params: vec![],
        indices: vec![],
        constructors: vec![true_con, false_con],
    })
}

#[test]
fn bool_formation() {
    let mut store = Store::new();
    let bool_tm = bool_def(&mut store);
    let ty = infer(&mut store, Ctx::empty(), bool_tm).unwrap();
    let ty0 = type0(&mut store);
    let ty0_val = nbe::eval(&mut store, None, ty0);
    assert!(nbe::conv(&mut store, 0, ty, ty0_val));
}

#[test]
fn bool_constructors() {
    let mut store = Store::new();
    let bool_tm = bool_def(&mut store);
    let bool_val = nbe::eval(&mut store, None, bool_tm);

    let true_tm = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    check(&mut store, Ctx::empty(), true_tm, bool_val).unwrap();

    let false_tm = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 1,
        args: vec![],
        indices: vec![],
    });
    check(&mut store, Ctx::empty(), false_tm, bool_val).unwrap();
}

#[test]
fn bool_case_true() {
    let mut store = Store::new();
    let bool_tm = bool_def(&mut store);

    let ty0 = type0(&mut store);
    let motive = store.terms.alloc(Term::Lam(ty0));

    let true_con = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    let false_con = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 1,
        args: vec![],
        indices: vec![],
    });

    let case_tm = store.terms.alloc(Term::Case {
        target: true_con,
        motive,
        branches: vec![true_con, false_con],
    });

    let nf = normalize(&mut store, case_tm);
    match store.terms.get(nf) {
        Term::Con { idx, .. } => assert_eq!(*idx, 0),
        other => panic!("expected Con (true), got {other:?}"),
    }
}

#[test]
fn bool_case_false() {
    let mut store = Store::new();
    let bool_tm = bool_def(&mut store);

    let ty0 = type0(&mut store);
    let motive = store.terms.alloc(Term::Lam(ty0));

    let true_con = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    let false_con = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 1,
        args: vec![],
        indices: vec![],
    });

    let case_tm = store.terms.alloc(Term::Case {
        target: false_con,
        motive,
        branches: vec![true_con, false_con],
    });

    let nf = normalize(&mut store, case_tm);
    match store.terms.get(nf) {
        Term::Con { idx, .. } => assert_eq!(*idx, 1),
        other => panic!("expected Con (false), got {other:?}"),
    }
}

fn unit_def(store: &mut Store) -> rock::TermId {
    let tt_con = ConstructorDef {
        name: "tt".to_string(),
        arg_types: vec![],
        recursive: vec![],
        indices: vec![],
    };
    store.terms.alloc(Term::Inductive {
        level: store.levels.alloc(rock::Level::Zero),
        params: vec![],
        indices: vec![],
        constructors: vec![tt_con],
    })
}

#[test]
fn unit_formation_and_constructors() {
    let mut store = Store::new();
    let unit_tm = unit_def(&mut store);
    let unit_val = nbe::eval(&mut store, None, unit_tm);

    let ty = infer(&mut store, Ctx::empty(), unit_tm).unwrap();
    let ty0 = type0(&mut store);
    let ty0_val = nbe::eval(&mut store, None, ty0);
    assert!(nbe::conv(&mut store, 0, ty, ty0_val));

    let tt = store.terms.alloc(Term::Con {
        def: unit_tm,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    check(&mut store, Ctx::empty(), tt, unit_val).unwrap();
}

#[test]
fn void_formation() {
    let mut store = Store::new();
    let void_tm = store.terms.alloc(Term::Inductive {
        level: store.levels.alloc(rock::Level::Zero),
        params: vec![],
        indices: vec![],
        constructors: vec![],
    });
    let ty = infer(&mut store, Ctx::empty(), void_tm).unwrap();
    let ty0 = type0(&mut store);
    let ty0_val = nbe::eval(&mut store, None, ty0);
    assert!(nbe::conv(&mut store, 0, ty, ty0_val));
}

#[test]
fn bool_neutral_case() {
    let mut store = Store::new();
    let bool_tm = bool_def(&mut store);
    let bool_val = nbe::eval(&mut store, None, bool_tm);

    let ctx = Ctx::empty().bind(&mut store, bool_val);
    let b = store.terms.alloc(Term::Var(0));

    let ty0 = type0(&mut store);
    let motive = store.terms.alloc(Term::Lam(ty0));

    let true_con = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    let false_con = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 1,
        args: vec![],
        indices: vec![],
    });

    let case_tm = store.terms.alloc(Term::Case {
        target: b,
        motive,
        branches: vec![true_con, false_con],
    });

    let val = nbe::eval(&mut store, ctx.env, case_tm);
    match store.values.get(val) {
        rock::Value::Neut(neut) => {
            assert_eq!(neut.level, 0);
            assert!(neut.spine.is_some());
        }
        other => panic!("expected neutral, got {other:?}"),
    }
}

// ===== Indexed inductive type tests =====

/// Helper: build the Vec inductive type definition.
/// data Vec (A : Set) : ℕ → Set where
///   nil  : Vec A zero
///   cons : (n : ℕ) → A → Vec A n → Vec A (suc n)
fn vec_def(store: &mut Store) -> rock::TermId {
    // De Bruijn scheme in constructor body context:
    // Var(0) = A (param), Var(1) = n (index), Var(2) = D (Vec itself)
    let l0 = store.levels.alloc(rock::Level::Zero);
    let nat_def_tm = nat_def(store);
    let zero = nat_zero(store, nat_def_tm);

    // nil: no constructor-specific args, index = zero
    let nil_con = ConstructorDef {
        name: "nil".to_string(),
        arg_types: vec![],
        recursive: vec![],
        indices: vec![zero],
    };

    // cons : (n' : Nat) → (a : A) → (v : Vec A n') → Vec A (suc n')
    //
    // Constructor arg types use the same de Bruijn scheme as the Inductive body.
    // In body_ctx: Var(0) = A (param), Var(1) = n (index = Nat), Var(2) = D (Vec)
    //
    // But arg types are checked sequentially with previous args bound:
    //   arg_types[0] (n' : Nat) checked in ctx(D, n, A):
    //     Var(0)=A, Var(1)=n, Var(2)=D  →  Nat type is nat_def_tm (closed term)
    //
    //   arg_types[1] (a : A) checked in ctx(D, n, A, n'):
    //     Var(0)=n', Var(1)=A, Var(2)=n, Var(3)=D  →  A = Var(1)
    //
    //   arg_types[2] (v : Vec A n') checked in ctx(D, n, A, n', a):
    //     Var(0)=a, Var(1)=n', Var(2)=A, Var(3)=n, Var(4)=D
    //     →  Vec A n' = App(App(Var(4), Var(2)), Var(1))

    // n' : Nat → use the Nat definition directly (closed term)
    let n_arg_ty = nat_def_tm;

    // a : A → Var(1) in ctx(D,n,A,n')
    let a_ty = store.terms.alloc(Term::Var(1));

    // v : Vec A n' = App(App(D, A), n') = App(App(Var(4), Var(2)), Var(1))
    let v_d = store.terms.alloc(Term::Var(4)); // D = Vec
    let v_a = store.terms.alloc(Term::Var(2)); // A
    let v_da = store.terms.alloc(Term::App(v_d, v_a)); // Vec A
    let v_n = store.terms.alloc(Term::Var(1)); // n'
    let vec_a = store.terms.alloc(Term::App(v_da, v_n)); // Vec A n'

    // Index expression for cons: suc n'
    // After binding all args: Var(0)=v, Var(1)=a, Var(2)=n', Var(3)=A, Var(4)=n, Var(5)=D
    // n' is at Var(2)
    let suc_n_arg = store.terms.alloc(Term::Var(2));
    let suc_n = store.terms.alloc(Term::Con {
        def: nat_def_tm,
        idx: 1,
        args: vec![suc_n_arg],
        indices: vec![],
    });

    let cons_con = ConstructorDef {
        name: "cons".to_string(),
        arg_types: vec![n_arg_ty, a_ty, vec_a],
        recursive: vec![false, false, true],
        indices: vec![suc_n],
    };

    let a_type = store.terms.alloc(Term::Univ(l0));
    store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![a_type],
        indices: vec![nat_def_tm],
        constructors: vec![nil_con, cons_con],
    })
}

#[test]
fn vec_formation() {
    let mut store = Store::new();
    let vec_tm = vec_def(&mut store);
    match infer(&mut store, Ctx::empty(), vec_tm) {
        Ok(ty) => {
            // Vec has params and indices, so its type is a Pi type
            println!("Vec type: {:?}", store.values.get(ty));
        }
        Err(e) => {
            panic!("Vec formation failed: {e:?}");
        }
    }
}

// Simple indexed type: BoolIdx indexed by Bool: data BoolIdx : Bool → Set where
//   btrue  : BoolIdx true
//   bfalse : BoolIdx false
fn simple_indexed_def(store: &mut Store) -> rock::TermId {
    let l0 = store.levels.alloc(rock::Level::Zero);
    let bool_tm = bool_def(store);

    let true_tm = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    let false_tm = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 1,
        args: vec![],
        indices: vec![],
    });

    store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![bool_tm],
        constructors: vec![
            ConstructorDef {
                name: "btrue".to_string(),
                arg_types: vec![],
                recursive: vec![],
                indices: vec![true_tm],
            },
            ConstructorDef {
                name: "bfalse".to_string(),
                arg_types: vec![],
                recursive: vec![],
                indices: vec![false_tm],
            },
        ],
    })
}

#[test]
fn simple_indexed_formation() {
    let mut store = Store::new();
    let tm = simple_indexed_def(&mut store);
    match infer(&mut store, Ctx::empty(), tm) {
        Ok(ty) => {
            println!("Simple indexed type: {:?}", store.values.get(ty));
        }
        Err(e) => {
            panic!("Simple indexed formation failed: {e:?}");
        }
    }
}

// ───────────────────────────────────────────────────────────────────────────
// Strict positivity tests
//
// Per AGENTS.md §4: for each accepted Inductive, a rejected sibling where the
// self-reference appears in a negative position.
//
// Citation: Coquand & Paulin (1988) §3 "Positivity condition".
// ───────────────────────────────────────────────────────────────────────────

/// Nat is accepted (recursive arg is directly D, i.e. strictly positive).
/// This test confirms that the positivity checker does not break legitimate
/// inductive types.
#[test]
fn positivity_nat_accepted() {
    let mut store = Store::new();
    let def = nat_def(&mut store);
    infer(&mut store, Ctx::empty(), def).unwrap();
}

/// Bool is accepted (no recursion at all).
#[test]
fn positivity_bool_accepted() {
    let mut store = Store::new();
    let bool_tm = bool_def(&mut store);
    infer(&mut store, Ctx::empty(), bool_tm).unwrap();
}

/// Vec is accepted (recursive arg `Vec A n` is an application of D to args
/// that do not themselves mention D — strictly positive).
#[test]
fn positivity_vec_accepted() {
    let mut store = Store::new();
    let vec_tm = vec_def(&mut store);
    infer(&mut store, Ctx::empty(), vec_tm).unwrap();
}

/// Negative case 1: D in domain of Pi (negative position).
///
/// data Bad1 : Type 0 where
///   bad : (Bad1 → Bool) → Bad1       -- domain is Bad1, negative position
///
/// In the body context D = Var(0), so the arg type `Pi(Var(0), bool_tm)` has D
/// in the domain.  The positivity checker must reject this.
///
/// Agda rejects: data Bad1 : Set where bad : (Bad1 → Bool) → Bad1
#[test]
fn positivity_negative_pi_domain() {
    let mut store = Store::new();
    let l0 = store.levels.alloc(rock::Level::Zero);
    let bool_tm = bool_def(&mut store);

    // arg type: Π(Var(0)) . bool_tm  i.e. (D → Bool)
    // In arg_types[0] of the first constructor, before binding any constructor
    // args, D is at: num_indices(0) + num_params(0) + k(0) = Var(0).
    let d_ref = store.terms.alloc(Term::Var(0));
    let neg_arg = store.terms.alloc(Term::Pi(d_ref, bool_tm));

    let bad1 = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "bad".to_string(),
            arg_types: vec![neg_arg],
            recursive: vec![false],
            indices: vec![],
        }],
    });

    assert!(
        matches!(
            infer(&mut store, Ctx::empty(), bad1),
            Err(TypeError::NotStrictlyPositive)
        ),
        "rock must reject D in Pi domain (negative position)"
    );
}

/// Negative case 2: D in left component of Sigma (Sigma is covariant, but the
/// occurrence is nested negatively via a Pi inside the Sigma's left field).
///
/// data Bad2 : Type 0 where
///   bad : ((Bad2 → Bool) × Bool) → Bad2
///
/// arg type: Σ(Pi(D, Bool)) . Bool — D is in the domain of an inner Pi, which
/// is in the left slot of Sigma.  Still negative.
#[test]
fn positivity_negative_sigma_left_contains_pi_domain() {
    let mut store = Store::new();
    let l0 = store.levels.alloc(rock::Level::Zero);
    let bool_tm = bool_def(&mut store);

    // inner type: Π(D) . Bool  — D in Pi domain
    let d_ref = store.terms.alloc(Term::Var(0));
    let pi_d_bool = store.terms.alloc(Term::Pi(d_ref, bool_tm));
    // Sigma left = pi_d_bool, right = bool
    let sigma_arg = store.terms.alloc(Term::Sigma(pi_d_bool, bool_tm));

    let bad2 = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "bad".to_string(),
            arg_types: vec![sigma_arg],
            recursive: vec![false],
            indices: vec![],
        }],
    });

    assert!(
        matches!(
            infer(&mut store, Ctx::empty(), bad2),
            Err(TypeError::NotStrictlyPositive)
        ),
        "rock must reject D in Pi domain nested inside Sigma left"
    );
}

/// Negative case 3: D in the right component of Sigma, in a negative position
/// (Pi domain inside the Sigma's right field).
///
/// data Bad3 : Type 0 where
///   bad : (Nat × (Bad3 → Bool)) → Bad3
///
/// arg type: Σ Nat (Pi(D_inner, Bool))
/// In the right field of Sigma, after one Sigma binder, D shifts to Var(1).
/// But the right field contains Π(D_inner) . Bool — D_inner in Pi domain,
/// negative.
///
/// In the body context at k=0: D = Var(0).
/// Sigma's left = nat_tm (D-free, ok).
/// Sigma's right = Pi(Var(1), bool_tm) — after crossing the Sigma binder,
/// d increments to 1, so Var(1) = D.  Pi domain = D → negative.
#[test]
fn positivity_negative_d_as_app_argument() {
    let mut store = Store::new();
    let l0 = store.levels.alloc(rock::Level::Zero);
    let nat_tm = nat_def(&mut store);
    let bool_tm = bool_def(&mut store);

    // Inside Sigma's right field, D is at Var(1) (Sigma adds one binder).
    // Pi(Var(1), bool_tm) — D in Pi domain (negative).
    let d_in_sigma = store.terms.alloc(Term::Var(1));
    let pi_d_bool = store.terms.alloc(Term::Pi(d_in_sigma, bool_tm));
    // Sigma: left = Nat, right = Pi(D, Bool)
    let neg_arg = store.terms.alloc(Term::Sigma(nat_tm, pi_d_bool));

    let bad3 = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "bad".to_string(),
            arg_types: vec![neg_arg],
            recursive: vec![false],
            indices: vec![],
        }],
    });

    assert!(
        matches!(
            infer(&mut store, Ctx::empty(), bad3),
            Err(TypeError::NotStrictlyPositive)
        ),
        "rock must reject D in Pi domain inside Sigma right field"
    );
}

/// Negative case 4: D in domain of a nested Pi inside the codomain.
///
/// data Bad4 : Type 0 where
///   bad : (Nat → (Bad4 → Bool)) → Bad4
///
/// arg type: Π(Nat) . Π(D) . Bool — outer Pi domain is Nat (fine),
/// inner Pi domain is D (negative).
///
/// In arg_types[0] (k=0), D = Var(0).  The term is:
///   Pi(nat_tm, Pi(Var(1), bool_tm))
/// where Var(1) refers to D after crossing the outer Pi binder.
#[test]
fn positivity_negative_nested_pi_domain() {
    let mut store = Store::new();
    let l0 = store.levels.alloc(rock::Level::Zero);
    let nat_tm = nat_def(&mut store);
    let bool_tm = bool_def(&mut store);

    // Inner: Π(D) . Bool  — inside the outer Pi, D is at Var(0+1)=Var(1)
    // (outer Pi introduces one binder, shifting D from Var(0) to Var(1))
    let d_inner = store.terms.alloc(Term::Var(1));
    let inner_pi = store.terms.alloc(Term::Pi(d_inner, bool_tm));
    // Outer: Π(Nat) . inner_pi
    let neg_arg = store.terms.alloc(Term::Pi(nat_tm, inner_pi));

    let bad4 = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "bad".to_string(),
            arg_types: vec![neg_arg],
            recursive: vec![false],
            indices: vec![],
        }],
    });

    assert!(
        matches!(
            infer(&mut store, Ctx::empty(), bad4),
            Err(TypeError::NotStrictlyPositive)
        ),
        "rock must reject D in domain of nested Pi"
    );
}

/// Positive Pi recursion is unsupported by the direct-argument eliminator.
///
/// data Good1 : Type 0 where
///   good : (Nat → Good1) → Good1    -- D only in codomain, positive
///
/// arg type: Π(Nat) . D  — D is in the codomain of Pi, not the domain.
/// D = Var(0) at k=0; after crossing the Pi binder, D = Var(1).
#[test]
fn positivity_function_recursion_is_unsupported() {
    let mut store = Store::new();
    let l0 = store.levels.alloc(rock::Level::Zero);
    let nat_tm = nat_def(&mut store);

    // D in codomain: after one Pi binder, D shifts to Var(1)
    let d_cod = store.terms.alloc(Term::Var(1));
    let good_arg = store.terms.alloc(Term::Pi(nat_tm, d_cod));

    let good1 = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "good".to_string(),
            arg_types: vec![good_arg],
            recursive: vec![false],
            indices: vec![],
        }],
    });

    assert_eq!(
        infer(&mut store, Ctx::empty(), good1),
        Err(TypeError::NotStrictlyPositive)
    );
}

#[test]
fn recursive_metadata_must_match_in_both_directions_and_at_consumers() {
    for (direct, flags) in [
        (false, vec![]),
        (false, vec![false, false]),
        (false, vec![true]),
        (true, vec![false]),
    ] {
        let mut store = Store::new();
        let l0 = store.levels.alloc(rock::Level::Zero);
        let bool_tm = bool_def(&mut store);
        let arg_ty = if direct {
            store.terms.alloc(Term::Var(0))
        } else {
            bool_tm
        };
        let def = store.terms.alloc(Term::Inductive {
            level: l0,
            params: vec![],
            indices: vec![],
            constructors: vec![ConstructorDef {
                name: "bad".into(),
                arg_types: vec![arg_ty],
                recursive: flags,
                indices: vec![],
            }],
        });
        assert_eq!(
            infer(&mut store, Ctx::empty(), def),
            Err(TypeError::InvalidRecursiveMetadata)
        );
        let value = nbe::eval(&mut store, None, def);
        let arg = store.terms.alloc(Term::Con {
            def: bool_tm,
            idx: 0,
            args: vec![],
            indices: vec![],
        });
        let con = store.terms.alloc(Term::Con {
            def,
            idx: 0,
            args: vec![arg],
            indices: vec![],
        });
        assert_eq!(
            infer(&mut store, Ctx::empty(), con),
            Err(TypeError::InvalidRecursiveMetadata)
        );
        assert_eq!(
            check(&mut store, Ctx::empty(), con, value),
            Err(TypeError::InvalidRecursiveMetadata)
        );
        // A neutral target bypasses constructor inference entirely.
        let ctx = Ctx::empty().bind(&mut store, value);
        let target = store.terms.alloc(Term::Var(0));
        let motive = store.terms.alloc(Term::Lam(bool_tm));
        let case = store.terms.alloc(Term::Case {
            target,
            motive,
            branches: vec![arg],
        });
        assert_eq!(
            infer(&mut store, ctx, case),
            Err(TypeError::InvalidRecursiveMetadata)
        );
    }
}

#[test]
fn nested_self_is_not_outer_self_after_constructor_and_pi_binders() {
    for capture_outer in [false, true] {
        let mut store = Store::new();
        let l0 = store.levels.alloc(rock::Level::Zero);
        let bool_tm = bool_def(&mut store);
        // Outer has an earlier Bool field; Inner adds self and a Bool field.
        // Before the Pi: inner field=0, Inner=1, outer field=2, Outer=3.
        // Its codomain adds one binder: Outer=4. A closed Nat control instead
        // has its own recursive Var(0), which must not be confused with Outer.
        let nested_arg = if capture_outer {
            let outer_ref = store.terms.alloc(Term::Var(4));
            store.terms.alloc(Term::Pi(bool_tm, outer_ref))
        } else {
            nat_def(&mut store)
        };
        let inner = store.terms.alloc(Term::Inductive {
            level: l0,
            params: vec![],
            indices: vec![],
            constructors: vec![ConstructorDef {
                name: "inner".into(),
                arg_types: vec![bool_tm, nested_arg],
                recursive: vec![false, false],
                indices: vec![],
            }],
        });
        let outer = store.terms.alloc(Term::Inductive {
            level: l0,
            params: vec![],
            indices: vec![],
            constructors: vec![ConstructorDef {
                name: "outer".into(),
                arg_types: vec![bool_tm, inner],
                recursive: vec![false, false],
                indices: vec![],
            }],
        });
        let result = infer(&mut store, Ctx::empty(), outer);
        if capture_outer {
            assert_eq!(result, Err(TypeError::NotStrictlyPositive));
        } else {
            result.unwrap();
        }
    }
}

#[test]
fn positive_sigma_recursion_is_unsupported() {
    let mut store = Store::new();
    let l0 = store.levels.alloc(rock::Level::Zero);
    let bool_tm = bool_def(&mut store);
    let d = store.terms.alloc(Term::Var(1));
    let arg = store.terms.alloc(Term::Sigma(bool_tm, d));
    let def = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "pair".into(),
            arg_types: vec![arg],
            recursive: vec![true],
            indices: vec![],
        }],
    });
    assert_eq!(
        infer(&mut store, Ctx::empty(), def),
        Err(TypeError::NotStrictlyPositive)
    );
}
