//! Differential testing harness: rock vs Agda 2.8.0 per AGENTS.md §3.1.

use std::path::Path;
use std::process::Command;

use rock::nbe::Store;
use rock::term::{ConstructorDef, Term};
use rock::{Ctx, check, infer, nat_def, nat_suc, nat_zero, normalize, type0};

const AGDA_BIN: &str = "/home/user/.cabal/bin/agda";

fn run_agda(case_name: &str) -> std::process::Output {
    let agda_path = if Path::new(AGDA_BIN).exists() {
        AGDA_BIN
    } else {
        "agda"
    };

    let case_file = format!("tests/differential/cases/{case_name}.agda");
    Command::new(agda_path)
        .arg("--no-libraries")
        .arg("-i")
        .arg("tests/differential/cases")
        .arg(&case_file)
        .output()
        .unwrap_or_else(|e| panic!("failed to execute agda on {case_file}: {e}"))
}

fn nat_numeral(store: &mut Store, def: rock::TermId, n: u32) -> rock::TermId {
    let mut tm = nat_zero(store, def);
    for _ in 0..n {
        tm = nat_suc(store, def, tm);
    }
    tm
}

fn bool_def_differential(store: &mut Store) -> rock::TermId {
    store.terms.alloc(Term::Inductive {
        level: store.levels.alloc(rock::Level::Zero),
        params: vec![],
        indices: vec![],
        constructors: vec![
            ConstructorDef {
                name: "true".to_string(),
                arg_types: vec![],
                recursive: vec![],
                indices: vec![],
            },
            ConstructorDef {
                name: "false".to_string(),
                arg_types: vec![],
                recursive: vec![],
                indices: vec![],
            },
        ],
    })
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
fn differential_positive_nat_matches_agda() {
    let output = run_agda("NatPositive");
    assert!(
        output.status.success(),
        "Agda rejected NatPositive.agda:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let mut store = Store::new();
    let def = nat_def(&mut store);

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

    check(&mut store, Ctx::empty(), add, add_ty_val).unwrap();

    let ann_add = store.terms.alloc(Term::Ann(add, add_ty));

    // (add 2 3) = 5
    let two = nat_numeral(&mut store, def, 2);
    let three = nat_numeral(&mut store, def, 3);
    let add_2 = store.terms.alloc(Term::App(ann_add, two));
    let add_2_3 = store.terms.alloc(Term::App(add_2, three));
    let nf_5 = normalize(&mut store, add_2_3);
    assert_nat_numeral(&store, nf_5, 5);

    // (add 0 5) = 5
    let zero = nat_zero(&mut store, def);
    let five = nat_numeral(&mut store, def, 5);
    let add_0 = store.terms.alloc(Term::App(ann_add, zero));
    let add_0_5 = store.terms.alloc(Term::App(add_0, five));
    let nf_0_5 = normalize(&mut store, add_0_5);
    assert_nat_numeral(&store, nf_0_5, 5);

    // Higher-order dependent recursion: addDep 3 4 = 7
    let pi_fn = store.terms.alloc(Term::Pi(def, def));
    let motive_fn = store.terms.alloc(Term::Lam(pi_fn));
    let vx = store.terms.alloc(Term::Var(0));
    let id_fn = store.terms.alloc(Term::Lam(vx));

    let vx0 = store.terms.alloc(Term::Var(0));
    let vih = store.terms.alloc(Term::Var(1));
    let app_ih_x = store.terms.alloc(Term::App(vih, vx0));
    let suc_app = nat_suc(&mut store, def, app_ih_x);
    let lam_x = store.terms.alloc(Term::Lam(suc_app));
    let lam_ih_dep = store.terms.alloc(Term::Lam(lam_x));
    let step_dep = store.terms.alloc(Term::Lam(lam_ih_dep));

    let rec_dep = store.terms.alloc(Term::Case {
        target: three,
        motive: motive_fn,
        branches: vec![id_fn, step_dep],
    });
    let four = nat_numeral(&mut store, def, 4);
    let app_dep = store.terms.alloc(Term::App(rec_dep, four));
    let nf_7 = normalize(&mut store, app_dep);
    assert_nat_numeral(&store, nf_7, 7);
}

#[test]
fn differential_negative_cases_rejected_by_both() {
    let mut store = Store::new();
    let ty0 = type0(&mut store);
    let def = nat_def(&mut store);

    // Case 1: suc applied to Set (Type 0)
    let agda1 = run_agda("NatNegative1");
    assert!(!agda1.status.success(), "Agda must reject NatNegative1");
    let bad1 = nat_suc(&mut store, def, ty0);
    assert!(
        infer(&mut store, Ctx::empty(), bad1).is_err(),
        "rock must reject bad1"
    );

    // Case 2: base case type mismatch in case (Set instead of Nat)
    let agda2 = run_agda("NatNegative2");
    assert!(!agda2.status.success(), "Agda must reject NatNegative2");
    let motive = store.terms.alloc(Term::Lam(def));
    let ih = store.terms.alloc(Term::Var(0));
    let suc_ih = nat_suc(&mut store, def, ih);
    let lam_suc = store.terms.alloc(Term::Lam(suc_ih));
    let step = store.terms.alloc(Term::Lam(lam_suc));
    let zero = nat_zero(&mut store, def);
    let bad2 = store.terms.alloc(Term::Case {
        target: zero,
        motive,
        branches: vec![ty0, step],
    });
    assert!(
        infer(&mut store, Ctx::empty(), bad2).is_err(),
        "rock must reject bad2"
    );

    // Case 3: step case wrong return type in case
    let agda3 = run_agda("NatNegative3");
    assert!(!agda3.status.success(), "Agda must reject NatNegative3");
    let pi_fn = store.terms.alloc(Term::Pi(def, def));
    let motive_fn = store.terms.alloc(Term::Lam(pi_fn));
    let vx = store.terms.alloc(Term::Var(0));
    let id_fn = store.terms.alloc(Term::Lam(vx));
    // Step returns zero (: Nat) instead of Nat -> Nat
    let lam_zero = store.terms.alloc(Term::Lam(zero));
    let bad_step = store.terms.alloc(Term::Lam(lam_zero));
    let bad3 = store.terms.alloc(Term::Case {
        target: zero,
        motive: motive_fn,
        branches: vec![id_fn, bad_step],
    });
    assert!(
        infer(&mut store, Ctx::empty(), bad3).is_err(),
        "rock must reject bad3"
    );

    // Case 4: target is Set instead of Nat
    let agda4 = run_agda("NatNegative4");
    assert!(!agda4.status.success(), "Agda must reject NatNegative4");
    let motive4 = store.terms.alloc(Term::Lam(def));
    let bad4 = store.terms.alloc(Term::Case {
        target: ty0,
        motive: motive4,
        branches: vec![zero, step],
    });
    assert!(
        infer(&mut store, Ctx::empty(), bad4).is_err(),
        "rock must reject bad4"
    );
}

#[test]
fn differential_positive_bool_matches_agda() {
    let output = run_agda("BoolPositive");
    assert!(
        output.status.success(),
        "Agda rejected BoolPositive.agda:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let mut store = Store::new();

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
    let bool_tm = store.terms.alloc(Term::Inductive {
        level: store.levels.alloc(rock::Level::Zero),
        params: vec![],
        indices: vec![],
        constructors: vec![true_con, false_con],
    });
    let bool_val = rock::eval(&mut store, None, bool_tm);

    let ty = infer(&mut store, Ctx::empty(), bool_tm).unwrap();
    let ty0 = type0(&mut store);
    let ty0_val = rock::eval(&mut store, None, ty0);
    assert!(rock::conv(&mut store, 0, ty, ty0_val));

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
    check(&mut store, Ctx::empty(), true_tm, bool_val).unwrap();
    check(&mut store, Ctx::empty(), false_tm, bool_val).unwrap();

    // not = λb. case b { true => false ; false => true }
    let motive = store.terms.alloc(Term::Lam(bool_tm));
    let target_var = store.terms.alloc(Term::Var(0));
    let case_body = store.terms.alloc(Term::Case {
        target: target_var,
        motive,
        branches: vec![false_tm, true_tm],
    });
    let not_tm = store.terms.alloc(Term::Lam(case_body));
    let not_ty = store.terms.alloc(Term::Pi(bool_tm, bool_tm));
    let not_ty_val = rock::eval(&mut store, None, not_ty);
    check(&mut store, Ctx::empty(), not_tm, not_ty_val).unwrap();

    // not true ≅ false
    let ann_not = store.terms.alloc(Term::Ann(not_tm, not_ty));
    let app_not_true = store.terms.alloc(Term::App(ann_not, true_tm));
    let nf = normalize(&mut store, app_not_true);
    match store.terms.get(nf) {
        Term::Con { idx, .. } => assert_eq!(*idx, 1, "not true should be false"),
        other => panic!("expected Con, got {other:?}"),
    }

    // not false ≅ true
    let app_not_false = store.terms.alloc(Term::App(ann_not, false_tm));
    let nf2 = normalize(&mut store, app_not_false);
    match store.terms.get(nf2) {
        Term::Con { idx, .. } => assert_eq!(*idx, 0, "not false should be true"),
        other => panic!("expected Con, got {other:?}"),
    }
}

// ===== Indexed inductive type differential tests =====

#[test]
fn differential_positive_vec_matches_agda() {
    let output = run_agda("VecPositive");
    assert!(
        output.status.success(),
        "Agda rejected VecPositive.agda:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let mut store = Store::new();
    let l0 = store.levels.alloc(rock::Level::Zero);
    let nat_tm = nat_def(&mut store);
    let bool_tm = bool_def_differential(&mut store);

    // Vec Bool zero = nil
    let vec_nil = store.terms.alloc(Term::Con {
        def: nat_tm,
        idx: 0,
        args: vec![],
        indices: vec![],
    });

    // Build Vec type: Pi(A : Type0). Pi(n : Nat). Type0
    // Pre-allocate inner terms to avoid nested mutable borrows of store.terms.
    let univ_l0 = store.terms.alloc(Term::Univ(l0));
    let cons_a = store.terms.alloc(Term::Var(1));             // a : A
    let cons_d = store.terms.alloc(Term::Var(4));             // D (self ref)
    let cons_a2 = store.terms.alloc(Term::Var(2));            // A
    let app_d_a = store.terms.alloc(Term::App(cons_d, cons_a2));
    let cons_n = store.terms.alloc(Term::Var(1));             // n
    let app_d_a_n = store.terms.alloc(Term::App(app_d_a, cons_n)); // Vec A n
    let cons_n2 = store.terms.alloc(Term::Var(2));
    let suc_n = store.terms.alloc(Term::Con {
        def: nat_tm,
        idx: 1,
        args: vec![cons_n2],
        indices: vec![],
    });
    let vec_ty = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![univ_l0],
        indices: vec![nat_tm],
        constructors: vec![
            ConstructorDef {
                name: "nil".to_string(),
                arg_types: vec![],
                recursive: vec![],
                indices: vec![vec_nil],
            },
            ConstructorDef {
                name: "cons".to_string(),
                arg_types: vec![
                    nat_tm,      // n : Nat
                    cons_a,      // a : A
                    app_d_a_n,   // Vec A n
                ],
                recursive: vec![false, false, true],
                indices: vec![suc_n],
            },
        ],
    });

    // Type check Vec definition
    let _ = infer(&mut store, Ctx::empty(), vec_ty).unwrap();
    let vec_val = rock::eval(&mut store, None, vec_ty);

    // nil : Vec Bool zero
    let nil_term = store.terms.alloc(Term::Con {
        def: vec_ty,
        idx: 0,
        args: vec![],
        indices: vec![vec_nil],
    });
    let vec_bool_nil = store.terms.alloc(Term::App(vec_ty, bool_tm));
    let nil_ty = store.terms.alloc(Term::App(vec_bool_nil, vec_nil));
    let nil_ty_val = rock::eval(&mut store, None, nil_ty);
    rock::check(&mut store, Ctx::empty(), nil_term, nil_ty_val).unwrap();

    // cons zero true nil : Vec Bool (suc zero)
    let one = store.terms.alloc(Term::Con {
        def: nat_tm,
        idx: 1,
        args: vec![vec_nil],
        indices: vec![],
    });
    let true_tm = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    let cons_term = store.terms.alloc(Term::Con {
        def: vec_ty,
        idx: 1,
        args: vec![vec_nil, true_tm, nil_term],
        indices: vec![],
    });
    let vec_bool_one = store.terms.alloc(Term::App(vec_ty, bool_tm));
    let one_ty = store.terms.alloc(Term::App(vec_bool_one, one));
    let one_ty_val = rock::eval(&mut store, None, one_ty);
    rock::check(&mut store, Ctx::empty(), cons_term, one_ty_val).unwrap();
}

#[test]
fn differential_negative_vec_rejected() {
    // VecNegative1: cons used with wrong result index (nil produces Vec zero, but cons produces suc)
    let agda1 = run_agda("VecNegative1");
    assert!(!agda1.status.success(), "Agda must reject VecNegative1");

    let mut store = Store::new();
    let l0 = store.levels.alloc(rock::Level::Zero);
    let nat_tm = nat_def(&mut store);
    let bool_tm = bool_def_differential(&mut store);

    let vec_nil = store.terms.alloc(Term::Con {
        def: nat_tm,
        idx: 0,
        args: vec![],
        indices: vec![],
    });

    // Pre-allocate inner terms to avoid nested mutable borrows of store.terms.
    let univ_l0 = store.terms.alloc(Term::Univ(l0));
    let var1 = store.terms.alloc(Term::Var(1));
    let var4 = store.terms.alloc(Term::Var(4));
    let var2_a = store.terms.alloc(Term::Var(2));
    let app_v4_v2 = store.terms.alloc(Term::App(var4, var2_a));
    let var1_b = store.terms.alloc(Term::Var(1));
    let app_inner = store.terms.alloc(Term::App(app_v4_v2, var1_b));
    let var2_b = store.terms.alloc(Term::Var(2));
    let suc_var2 = store.terms.alloc(Term::Con {
        def: nat_tm,
        idx: 1,
        args: vec![var2_b],
        indices: vec![],
    });

    let vec_ty = store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![univ_l0],
        indices: vec![nat_tm],
        constructors: vec![
            ConstructorDef {
                name: "nil".to_string(),
                arg_types: vec![],
                recursive: vec![],
                indices: vec![vec_nil],
            },
            ConstructorDef {
                name: "cons".to_string(),
                arg_types: vec![
                    nat_tm,
                    var1,
                    app_inner,
                ],
                recursive: vec![false, false, true],
                indices: vec![suc_var2],
            },
        ],
    });
    let _ = infer(&mut store, Ctx::empty(), vec_ty).unwrap();

    // Bad: cons zero true nil : Vec Bool zero  (should be suc zero)
    let nil_term = store.terms.alloc(Term::Con {
        def: vec_ty,
        idx: 0,
        args: vec![],
        indices: vec![vec_nil],
    });
    let true_tm = store.terms.alloc(Term::Con {
        def: bool_tm,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    let bad_cons = store.terms.alloc(Term::Con {
        def: vec_ty,
        idx: 1,
        args: vec![vec_nil, true_tm, nil_term],
        indices: vec![],
    });
    // Type it as Vec Bool zero (wrong — should be suc zero)
    let vec_bool = store.terms.alloc(Term::App(vec_ty, bool_tm));
    let zero_ty = store.terms.alloc(Term::App(vec_bool, vec_nil));
    let zero_ty_val = rock::eval(&mut store, None, zero_ty);
    assert!(
        rock::check(&mut store, Ctx::empty(), bad_cons, zero_ty_val).is_err(),
        "rock must reject cons with wrong result index"
    );

    // VecNegative2: recursive arg has wrong index
    let agda2 = run_agda("VecNegative2");
    assert!(!agda2.status.success(), "Agda must reject VecNegative2");

    // bad = cons zero true (cons (suc zero) true nil)
    // The inner cons produces Vec Bool (suc (suc zero)), but outer needs Vec Bool zero
    let inner_nil = store.terms.alloc(Term::Con {
        def: vec_ty,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    let inner_cons = store.terms.alloc(Term::Con {
        def: vec_ty,
        idx: 1,
        args: vec![vec_nil, true_tm, inner_nil],
        indices: vec![],
    });
    let bad_cons2 = store.terms.alloc(Term::Con {
        def: vec_ty,
        idx: 1,
        args: vec![vec_nil, true_tm, inner_cons],
        indices: vec![],
    });
    // The inner cons has type Vec Bool (suc zero), but outer needs Vec Bool zero
    assert!(
        rock::check(&mut store, Ctx::empty(), bad_cons2, zero_ty_val).is_err(),
        "rock must reject cons with wrong recursive arg index"
    );
}

#[test]
fn differential_positive_boolidx_matches_agda() {
    let output = run_agda("BoolIdxPositive");
    assert!(
        output.status.success(),
        "Agda rejected BoolIdxPositive.agda:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let mut store = Store::new();
    let l0 = store.levels.alloc(rock::Level::Zero);
    let bool_tm = bool_def_differential(&mut store);

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

    // BoolIdx : Bool -> Type0
    let boolidx_ty = store.terms.alloc(Term::Inductive {
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
    });

    let _ = infer(&mut store, Ctx::empty(), boolidx_ty).unwrap();

    // btrue : BoolIdx true
    let btrue = store.terms.alloc(Term::Con {
        def: boolidx_ty,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    let btrue_ty = store.terms.alloc(Term::App(boolidx_ty, true_tm));
    let btrue_ty_val = rock::eval(&mut store, None, btrue_ty);
    rock::check(&mut store, Ctx::empty(), btrue, btrue_ty_val).unwrap();

    // bfalse : BoolIdx false
    let bfalse = store.terms.alloc(Term::Con {
        def: boolidx_ty,
        idx: 1,
        args: vec![],
        indices: vec![],
    });
    let bfalse_ty = store.terms.alloc(Term::App(boolidx_ty, false_tm));
    let bfalse_ty_val = rock::eval(&mut store, None, bfalse_ty);
    rock::check(&mut store, Ctx::empty(), bfalse, bfalse_ty_val).unwrap();
}

#[test]
fn differential_negative_boolidx_rejected() {
    let agda = run_agda("BoolIdxNegative1");
    assert!(!agda.status.success(), "Agda must reject BoolIdxNegative1");

    let mut store = Store::new();
    let l0 = store.levels.alloc(rock::Level::Zero);
    let bool_tm = bool_def_differential(&mut store);

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

    let boolidx_ty = store.terms.alloc(Term::Inductive {
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
    });
    let _ = infer(&mut store, Ctx::empty(), boolidx_ty).unwrap();

    // Bad: btrue typed as BoolIdx false (wrong index)
    let btrue = store.terms.alloc(Term::Con {
        def: boolidx_ty,
        idx: 0,
        args: vec![],
        indices: vec![],
    });
    let bad_ty = store.terms.alloc(Term::App(boolidx_ty, false_tm));
    let bad_ty_val = rock::eval(&mut store, None, bad_ty);
    assert!(
        rock::check(&mut store, Ctx::empty(), btrue, bad_ty_val).is_err(),
        "rock must reject btrue at wrong index"
    );
}
