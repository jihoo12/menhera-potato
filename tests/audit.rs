use rock::nbe::{self, Store};
use rock::term::{ConstructorDef, Term};
use rock::{
    Ctx, TypeError, check, infer, nat_def, type_n, type0,
};

fn empty_def(store: &mut Store) -> rock::TermId {
    let l0 = store.levels.alloc(rock::Level::Zero);
    store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![],
    })
}

fn bool_def_local(store: &mut Store) -> rock::TermId {
    let l0 = store.levels.alloc(rock::Level::Zero);

    let t = ConstructorDef {
        name: "true".into(),
        arg_types: vec![],
        recursive: vec![],
        indices: vec![],
    };

    let f = ConstructorDef {
        name: "false".into(),
        arg_types: vec![],
        recursive: vec![],
        indices: vec![],
    };

    store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![t, f],
    })
}

// -----------------------------------------------------------------------------
// A. Ordinary typing sanity
// -----------------------------------------------------------------------------

#[test]
fn audit_empty_is_not_an_inhabitant_of_itself() {
    let mut store = Store::new();

    let empty = empty_def(&mut store);
    let empty_val = nbe::eval(&mut store, None, empty);

    assert!(
        check(&mut store, Ctx::empty(), empty, empty_val).is_err(),
        "UNSOUND: Empty was accepted as an inhabitant of Empty"
    );
}

#[test]
fn audit_nat_is_not_an_inhabitant_of_itself() {
    let mut store = Store::new();

    let nat = nat_def(&mut store);
    let nat_val = nbe::eval(&mut store, None, nat);

    assert!(
        check(&mut store, Ctx::empty(), nat, nat_val).is_err(),
        "UNSOUND: Nat was accepted as an inhabitant of Nat"
    );
}

#[test]
fn audit_type0_is_not_type0() {
    let mut store = Store::new();

    let tm = type0(&mut store);
    let ty = type0(&mut store);
    let ty_val = nbe::eval(&mut store, None, ty);

    assert!(
        check(&mut store, Ctx::empty(), tm, ty_val).is_err(),
        "UNSOUND: Type0 : Type0"
    );
}

#[test]
fn audit_type1_is_not_type0() {
    let mut store = Store::new();

    let tm = type_n(&mut store, 1);
    let ty0 = type0(&mut store);
    let ty0_val = nbe::eval(&mut store, None, ty0);

    assert!(
        check(&mut store, Ctx::empty(), tm, ty0_val).is_err(),
        "UNSOUND: Type1 : Type0"
    );
}

#[test]
fn audit_type0_is_allowed_in_type2() {
    let mut store = Store::new();

    let tm = type0(&mut store);
    let ty2 = type_n(&mut store, 2);
    let ty2_val = nbe::eval(&mut store, None, ty2);

    check(&mut store, Ctx::empty(), tm, ty2_val)
        .expect("control failed: cumulativity Type0 : Type2 should hold");
}

// -----------------------------------------------------------------------------
// B. Closure/environment conversion
// -----------------------------------------------------------------------------

#[test]
fn audit_conversion_distinguishes_different_captures() {
    let mut store = Store::new();

    // λx. captured
    //
    // body Var(1):
    //   Var(0) = lambda argument
    //   Var(1) = captured variable
    let body = store.terms.alloc(Term::Var(1));

    let captured_a = nbe::fresh_var(&mut store, 0);
    let captured_b = nbe::fresh_var(&mut store, 1);

    let env_a = store.envs.alloc(rock::Env {
        parent: None,
        value: captured_a,
    });

    let env_b = store.envs.alloc(rock::Env {
        parent: None,
        value: captured_b,
    });

    let lam_a = store.values.alloc(rock::Value::Lam(rock::Closure {
        env: Some(env_a),
        body,
    }));

    let lam_b = store.values.alloc(rock::Value::Lam(rock::Closure {
        env: Some(env_b),
        body,
    }));

    assert!(
        !nbe::conv(&mut store, 2, lam_a, lam_b),
        "UNSOUND: lambdas capturing different variables were convertible"
    );
}

#[test]
fn audit_conversion_accepts_same_capture() {
    let mut store = Store::new();

    let body = store.terms.alloc(Term::Var(1));
    let captured = nbe::fresh_var(&mut store, 0);

    let env_a = store.envs.alloc(rock::Env {
        parent: None,
        value: captured,
    });
    let env_b = store.envs.alloc(rock::Env {
        parent: None,
        value: captured,
    });

    let lam_a = store.values.alloc(rock::Value::Lam(rock::Closure {
        env: Some(env_a),
        body,
    }));
    let lam_b = store.values.alloc(rock::Value::Lam(rock::Closure {
        env: Some(env_b),
        body,
    }));

    assert!(nbe::conv(&mut store, 1, lam_a, lam_b));
}

// -----------------------------------------------------------------------------
// C. Strict positivity
// -----------------------------------------------------------------------------

#[test]
fn audit_nested_inductive_cannot_hide_negative_outer_occurrence() {
    let mut store = Store::new();

    let l0 = store.levels.alloc(rock::Level::Zero);
    let bool_tm = bool_def_local(&mut store);

    // We are constructing:
    //
    // data Outer : Type where
    //   wrap : Inner -> Outer
    //
    // where Inner contains:
    //
    // data Inner : Type where
    //   mk : (Outer -> Bool) -> Inner
    //
    // Inside Inner's constructor context:
    //   Var(0) = Inner
    //   Var(1) = Outer
    //
    // So the negative occurrence of Outer is hidden inside a nested inductive.

    let outer_ref_inside_inner = store.terms.alloc(Term::Var(1));
    let outer_to_bool =
        store.terms.alloc(Term::Pi(outer_ref_inside_inner, bool_tm));

    let inner = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "mk".into(),
            arg_types: vec![outer_to_bool],
            recursive: vec![false],
            indices: vec![],
        }],
    });

    let outer = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "wrap".into(),
            arg_types: vec![inner],
            recursive: vec![false],
            indices: vec![],
        }],
    });

    assert!(
        matches!(
            infer(&mut store, Ctx::empty(), outer),
            Err(TypeError::NotStrictlyPositive)
        ),
        "UNSOUND: a nested inductive hid a negative occurrence of the outer type"
    );
}

// -----------------------------------------------------------------------------
// D. Untrusted recursive metadata
// -----------------------------------------------------------------------------

#[test]
fn audit_recursive_metadata_length_mismatch_is_rejected() {
    let mut store = Store::new();

    let l0 = store.levels.alloc(rock::Level::Zero);
    let bool_tm = bool_def_local(&mut store);

    let malformed = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "bad".into(),

            // one argument
            arg_types: vec![bool_tm],

            // but zero recursion flags
            recursive: vec![],

            indices: vec![],
        }],
    });

    assert!(
        infer(&mut store, Ctx::empty(), malformed).is_err(),
        "kernel accepted recursive.len() != arg_types.len()"
    );
}

#[test]
fn audit_nonrecursive_argument_cannot_be_marked_recursive() {
    let mut store = Store::new();

    let l0 = store.levels.alloc(rock::Level::Zero);
    let bool_tm = bool_def_local(&mut store);

    let malformed = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![ConstructorDef {
            name: "bad".into(),
            arg_types: vec![bool_tm],

            // Bool argument is not recursive, but metadata lies.
            recursive: vec![true],

            indices: vec![],
        }],
    });

    assert!(
        infer(&mut store, Ctx::empty(), malformed).is_err(),
        "kernel trusted false recursive metadata"
    );
}

// -----------------------------------------------------------------------------
// E. Constructor integrity
// -----------------------------------------------------------------------------

#[test]
fn audit_constructor_out_of_range_is_rejected() {
    let mut store = Store::new();

    let bool_tm = bool_def_local(&mut store);
    let bool_val = nbe::eval(&mut store, None, bool_tm);

    let impossible_constructor = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 999,
        args: vec![],
        indices: vec![],
    });

    assert!(
        check(
            &mut store,
            Ctx::empty(),
            impossible_constructor,
            bool_val
        )
        .is_err(),
        "kernel accepted an out-of-range constructor index"
    );
}

#[test]
fn audit_constructor_from_wrong_datatype_is_rejected() {
    let mut store = Store::new();

    let bool_tm = bool_def_local(&mut store);
    let empty_tm = empty_def(&mut store);

    let empty_val = nbe::eval(&mut store, None, empty_tm);

    let true_tm = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 0,
        args: vec![],
        indices: vec![],
    });

    assert!(
        check(&mut store, Ctx::empty(), true_tm, empty_val).is_err(),
        "UNSOUND: constructor of Bool inhabited Empty"
    );
}

// -----------------------------------------------------------------------------
// F. NbE / conversion invariants
// -----------------------------------------------------------------------------

#[test]
fn audit_conv_is_reflexive_on_open_neutral() {
    let mut store = Store::new();

    let x = nbe::fresh_var(&mut store, 0);

    assert!(
        nbe::conv(&mut store, 1, x, x),
        "conversion is not reflexive"
    );
}

#[test]
fn audit_conv_is_symmetric_on_distinct_neutrals() {
    let mut store = Store::new();

    let x = nbe::fresh_var(&mut store, 0);
    let y = nbe::fresh_var(&mut store, 1);

    let xy = nbe::conv(&mut store, 2, x, y);
    let yx = nbe::conv(&mut store, 2, y, x);

    assert_eq!(xy, yx, "conversion symmetry violated");
    assert!(!xy);
}

#[test]
fn audit_quote_eval_identity_lambda_roundtrip() {
    let mut store = Store::new();

    let x = store.terms.alloc(Term::Var(0));
    let id = store.terms.alloc(Term::Lam(x));

    let val = nbe::eval(&mut store, None, id);
    let quoted = nbe::quote(&mut store, 0, val);
    let val2 = nbe::eval(&mut store, None, quoted);

    assert!(
        nbe::conv(&mut store, 0, val, val2),
        "quote(eval(t)) changed the semantic value"
    );
}