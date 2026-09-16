//! Second-pass public-AST regressions (no fabricated semantic values).
use rock::{ConstructorDef, Ctx, Level, Store, Term, TermId, check, infer, nbe, type0};

fn data(s: &mut Store, fields: Vec<TermId>) -> TermId {
    let level = s.levels.alloc(Level::Zero);
    s.terms.alloc(Term::Inductive {
        level,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "pack".into(),
            recursive: vec![false; fields.len()],
            arg_types: fields,
            indices: vec![],
        }],
    })
}

#[test]
fn constructor_field_universe_must_fit_inductive_universe() {
    let mut s = Store::new();
    let u = type0(&mut s);
    let bad = data(&mut s, vec![u]); // Bad : Type0, pack : Type0 -> Bad
    assert!(
        infer(&mut s, Ctx::empty(), bad).is_err(),
        "accepted a Type1-sized field in Type0"
    );
}

#[test]
fn captured_inductive_definitions_cannot_be_conflated() {
    let mut s = Store::new();
    let u = type0(&mut s);
    let a = s.terms.alloc(Term::Var(1)); // under self, captures outer A
    let d = data(&mut s, vec![a]);
    let family = s.terms.alloc(Term::Lam(d));
    let family_ty = s.terms.alloc(Term::Pi(u, u));
    let family = s.terms.alloc(Term::Ann(family, family_ty));
    let nat = rock::nat_def(&mut s);
    let l = s.levels.alloc(Level::Zero);
    let empty = s.terms.alloc(Term::Inductive {
        level: l,
        params: vec![],
        indices: vec![],
        constructors: vec![],
    });
    let box_nat = s.terms.alloc(Term::App(family, nat));
    let box_empty = s.terms.alloc(Term::App(family, empty));
    let cast_ty = s.terms.alloc(Term::Pi(box_nat, box_empty));
    let x = s.terms.alloc(Term::Var(0));
    let identity = s.terms.alloc(Term::Lam(x));
    let cast = s.terms.alloc(Term::Ann(identity, cast_ty));
    assert!(
        infer(&mut s, Ctx::empty(), cast).is_err(),
        "accepted identity : Box Nat -> Box Empty"
    );
}

#[test]
fn same_logical_context_can_be_reconstructed_for_conversion() {
    let mut s = Store::new();
    let u = type0(&mut s);
    let ty = rock::check_is_type(&mut s, Ctx::empty(), u).unwrap();
    // Two representations of the SAME context A : Type0, not two locals in
    // one context. Both expressions denote its sole logical variable A.
    let first = Ctx::empty().bind(&mut s, ty);
    let second = Ctx::empty().bind(&mut s, ty);
    let a = s.terms.alloc(Term::Var(0));
    infer(&mut s, first, a).unwrap();
    infer(&mut s, second, a).unwrap();
    let av = nbe::eval(&mut s, first.env, a);
    let quoted = nbe::quote(&mut s, first.depth, av);
    let bv = nbe::eval(&mut s, second.env, quoted);
    assert!(
        nbe::conv(&mut s, 1, av, bv),
        "allocation identity changed the meaning of A"
    );
}

#[test]
fn explicit_constructor_indices_do_not_change_definitional_equality() {
    let mut s = Store::new();
    let nat = rock::nat_def(&mut s);
    let z = rock::nat_zero(&mut s, nat);
    let level = s.levels.alloc(Level::Zero);
    let d = s.terms.alloc(Term::Inductive {
        level,
        params: vec![],
        indices: vec![nat],
        constructors: vec![ConstructorDef {
            name: "c".into(),
            arg_types: vec![],
            recursive: vec![],
            indices: vec![z],
        }],
    });
    let omitted = s.terms.alloc(Term::Con {
        def: d,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    let explicit = s.terms.alloc(Term::Con {
        def: d,
        idx: 0,
        args: vec![],
        indices: vec![z],
    });
    let dz = s.terms.alloc(Term::App(d, z));
    let u = type0(&mut s);
    let f_ty = s.terms.alloc(Term::Pi(dz, u));
    let f0 = s.terms.alloc(Term::Var(0));
    let f1 = s.terms.alloc(Term::Var(1));
    let dom = s.terms.alloc(Term::App(f0, omitted));
    let cod = s.terms.alloc(Term::App(f1, explicit));
    let cast = s.terms.alloc(Term::Pi(dom, cod));
    let ty = s.terms.alloc(Term::Pi(f_ty, cast));
    let x = s.terms.alloc(Term::Var(0));
    let id = s.terms.alloc(Term::Lam(x));
    let term = s.terms.alloc(Term::Lam(id));
    let ann = s.terms.alloc(Term::Ann(term, ty));
    infer(&mut s, Ctx::empty(), ann).expect("optional checked indices are annotations");
}

fn roundtrip(s: &mut Store, ctx: Ctx, tm: TermId) {
    let ty = infer(s, ctx, tm).expect("probe must be a checked term");
    let a = nbe::eval(s, ctx.env, tm);
    let q = nbe::quote(s, ctx.depth, a);
    check(s, ctx, q, ty).expect("quote preserves the checked type");
    let b = nbe::eval(s, ctx.env, q);
    let q2 = nbe::quote(s, ctx.depth, b);
    check(s, ctx, q2, ty).unwrap();
    let c = nbe::eval(s, ctx.env, q2);
    // This finite equivalence-class probe exercises reflexivity, both
    // directions, and the a~b~c => a~c instance of transitivity.
    for x in [a, b, c] {
        for y in [a, b, c] {
            assert!(nbe::conv(s, ctx.depth, x, y));
        }
    }
}

#[test]
fn checked_neutral_spines_closures_eta_and_roundtrips() {
    let mut s = Store::new();
    let nat = rock::nat_def(&mut s);
    let nat_ty = rock::check_is_type(&mut s, Ctx::empty(), nat).unwrap();
    let function_ty = s.terms.alloc(Term::Pi(nat, nat));
    let function_val = rock::check_is_type(&mut s, Ctx::empty(), function_ty).unwrap();
    let pair_ty = s.terms.alloc(Term::Sigma(nat, nat));
    let pair_val = rock::check_is_type(&mut s, Ctx::empty(), pair_ty).unwrap();
    let ctx = Ctx::empty()
        .bind(&mut s, nat_ty)
        .bind(&mut s, function_val)
        .bind(&mut s, pair_val);
    // n : Nat, f : Nat -> Nat, p : Nat * Nat
    let n = s.terms.alloc(Term::Var(2));
    let f = s.terms.alloc(Term::Var(1));
    let p = s.terms.alloc(Term::Var(0));
    let app = s.terms.alloc(Term::App(f, n));
    let fst = s.terms.alloc(Term::Fst(p));
    let snd = s.terms.alloc(Term::Snd(p));
    let pair = s.terms.alloc(Term::Pair(fst, snd));
    let pair = s.terms.alloc(Term::Ann(pair, pair_ty));
    let f_under_lambda = s.terms.alloc(Term::Var(2));
    let x = s.terms.alloc(Term::Var(0));
    let fx = s.terms.alloc(Term::App(f_under_lambda, x));
    let eta = s.terms.alloc(Term::Lam(fx));
    let eta = s.terms.alloc(Term::Ann(eta, function_ty));
    let motive = s.terms.alloc(Term::Lam(nat));
    let z = rock::nat_zero(&mut s, nat);
    let ih = s.terms.alloc(Term::Var(0));
    let succ = rock::nat_suc(&mut s, nat, ih);
    let ih_lam = s.terms.alloc(Term::Lam(succ));
    let branch = s.terms.alloc(Term::Lam(ih_lam));
    let case = s.terms.alloc(Term::Case {
        target: n,
        motive,
        branches: vec![z, branch],
    });
    let mixed = s.terms.alloc(Term::App(f, case));
    for tm in [
        n,
        f,
        p,
        app,
        fst,
        snd,
        pair,
        eta,
        case,
        mixed,
        function_ty,
        pair_ty,
    ] {
        roundtrip(&mut s, ctx, tm);
    }
    for (a, b) in [(f, eta), (p, pair)] {
        let a = nbe::eval(&mut s, ctx.env, a);
        let b = nbe::eval(&mut s, ctx.env, b);
        assert!(nbe::conv(&mut s, ctx.depth, a, b));
        assert!(nbe::conv(&mut s, ctx.depth, b, a));
    }
    // Beta substitution preserves an outer capture: (lambda _:Nat. n) zero.
    let captured = s.terms.alloc(Term::Var(3));
    let lam = s.terms.alloc(Term::Lam(captured));
    let lam = s.terms.alloc(Term::Ann(lam, function_ty));
    let beta = s.terms.alloc(Term::App(lam, z));
    roundtrip(&mut s, ctx, beta);
    let beta_v = nbe::eval(&mut s, ctx.env, beta);
    let n_v = nbe::eval(&mut s, ctx.env, n);
    assert!(nbe::conv(&mut s, ctx.depth, beta_v, n_v));
    let eta_app = s.terms.alloc(Term::App(eta, n));
    infer(&mut s, ctx, eta_app).unwrap();
    let eta_app = nbe::eval(&mut s, ctx.env, eta_app);
    let app = nbe::eval(&mut s, ctx.env, app);
    assert!(nbe::conv(&mut s, ctx.depth, eta_app, app));
}

#[test]
fn closed_checked_term_cannot_conflate_distinct_locals() {
    let mut s = Store::new();
    let u = type0(&mut s);
    // (A B : Type0) -> A -> B, purportedly inhabited by lambda A B x. x.
    let a = s.terms.alloc(Term::Var(1));
    let b = s.terms.alloc(Term::Var(1)); // under x, B is index 1
    let body_ty = s.terms.alloc(Term::Pi(a, b));
    let inner = s.terms.alloc(Term::Pi(u, body_ty));
    let ty = s.terms.alloc(Term::Pi(u, inner));
    let x = s.terms.alloc(Term::Var(0));
    let mut tm = x;
    for _ in 0..3 {
        tm = s.terms.alloc(Term::Lam(tm));
    }
    let ann = s.terms.alloc(Term::Ann(tm, ty));
    assert_eq!(
        infer(&mut s, Ctx::empty(), ann),
        Err(rock::TypeError::ConversionFailure)
    );
}

#[test]
fn explicit_parameter_box_is_supported_and_preserves_arguments() {
    let mut s = Store::new();
    let u = type0(&mut s);
    let a = s.terms.alloc(Term::Var(0)); // explicit parameter inside body
    let level = s.levels.alloc(Level::Zero);
    let d = s.terms.alloc(Term::Inductive {
        level,
        params: vec![u],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "box".into(),
            arg_types: vec![a],
            recursive: vec![false],
            indices: vec![],
        }],
    });
    infer(&mut s, Ctx::empty(), d).unwrap();
    let nat = rock::nat_def(&mut s);
    let z = rock::nat_zero(&mut s, nat);
    let ty = s.terms.alloc(Term::App(d, nat));
    let c = s.terms.alloc(Term::Con {
        def: d,
        idx: 0,
        args: vec![z],
        indices: vec![],
    });
    let ann = s.terms.alloc(Term::Ann(c, ty));
    roundtrip(&mut s, Ctx::empty(), ann);
    let empty = s.terms.alloc(Term::Inductive {
        level,
        params: vec![],
        indices: vec![],
        constructors: vec![],
    });
    let other = s.terms.alloc(Term::App(d, empty));
    let bad = s.terms.alloc(Term::Ann(ann, other));
    assert!(infer(&mut s, Ctx::empty(), bad).is_err());
}

#[test]
fn field_bound_applies_through_constructor_entry_and_allows_large_declarations() {
    let mut s = Store::new();
    let u = type0(&mut s);
    let small = data(&mut s, vec![u]);
    let nat = rock::nat_def(&mut s);
    let c = s.terms.alloc(Term::Con {
        def: small,
        idx: 0,
        args: vec![nat],
        indices: vec![],
    });
    assert_eq!(
        infer(&mut s, Ctx::empty(), c),
        Err(rock::TypeError::LevelMismatch)
    );
    let large_level = s.levels.alloc(Level::Zero);
    let large_level = s.levels.alloc(Level::Suc(large_level));
    // Build a new AST; no mutation of an already checked definition.
    let mut large = s.terms.get(small).clone();
    if let Term::Inductive { level, .. } = &mut large {
        *level = large_level;
    }
    let large = s.terms.alloc(large);
    infer(&mut s, Ctx::empty(), large).unwrap();
    let c = s.terms.alloc(Term::Con {
        def: large,
        idx: 0,
        args: vec![nat],
        indices: vec![],
    });
    roundtrip(&mut s, Ctx::empty(), c);
}
