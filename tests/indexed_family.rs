//! Dependent signature/result telescopes and uniform unary indexed elimination.
#[path = "differential/branch_reference.rs"]
mod reference;
use rock::nbe::{self, Store};
use rock::{ConstructorDef, Ctx, Level, Term, TermId, TypeError, Value, check, infer, normalize};
fn v(s: &mut Store, i: u32) -> TermId {
    s.terms.alloc(Term::Var(i))
}
fn ctor(args: Vec<TermId>, recursive: Vec<bool>, indices: Vec<TermId>) -> ConstructorDef {
    ConstructorDef {
        name: "c".into(),
        arg_types: args,
        recursive,
        indices,
    }
}
fn data(
    s: &mut Store,
    params: Vec<TermId>,
    indices: Vec<TermId>,
    cs: Vec<ConstructorDef>,
) -> TermId {
    let level = s.levels.alloc(Level::Zero);
    let level = s.levels.alloc(Level::Suc(level));
    s.terms.alloc(Term::Inductive {
        level,
        params,
        indices,
        constructors: cs,
    })
}
fn bool_def(s: &mut Store) -> TermId {
    let level = s.levels.alloc(Level::Zero);
    s.terms.alloc(Term::Inductive {
        level,
        params: vec![],
        indices: vec![],
        constructors: vec![ctor(vec![], vec![], vec![]), ctor(vec![], vec![], vec![])],
    })
}
fn con(s: &mut Store, def: TermId, idx: usize, args: Vec<TermId>) -> TermId {
    s.terms.alloc(Term::Con {
        def,
        idx,
        args,
        indices: vec![],
    })
}
fn app(s: &mut Store, mut f: TermId, args: &[TermId]) -> TermId {
    for &a in args {
        f = s.terms.alloc(Term::App(f, a));
    }
    f
}

#[test]
fn dependent_parameters_and_result_indices_share_values() {
    reference::assert_agda("IndexedScopes", true, "");
    let mut s = Store::new();
    let u = rock::type0(&mut s);
    let prev = v(&mut s, 0);
    // Body: self, B, index, A, a. Field b:A uses A=Var(1).
    let a_field = v(&mut s, 1);
    let a_result = v(&mut s, 2);
    let b_result = v(&mut s, 0);
    let def = data(
        &mut s,
        vec![u, prev],
        vec![u, prev],
        vec![ctor(vec![a_field], vec![false], vec![a_result, b_result])],
    );
    infer(&mut s, Ctx::empty(), def).unwrap();
    let bool_ = bool_def(&mut s);
    let t = con(&mut s, bool_, 0, vec![]);
    let f = con(&mut s, bool_, 1, vec![]);
    let ty = app(&mut s, def, &[bool_, t, bool_, f]);
    infer(&mut s, Ctx::empty(), ty).unwrap();
    let ty = nbe::eval(&mut s, None, ty);
    let term = con(&mut s, def, 0, vec![f]);
    check(&mut s, Ctx::empty(), term, ty).unwrap();
    assert_eq!(
        infer(&mut s, Ctx::empty(), term),
        Err(TypeError::CannotInferParameters)
    );
    let bad = con(&mut s, def, 0, vec![t]);
    assert!(check(&mut s, Ctx::empty(), bad, ty).is_err());
}

#[test]
fn earlier_result_index_instantiates_later_declared_index_type() {
    reference::assert_agda("IndexedScopes", true, "");
    reference::assert_agda("IndexedBadDependentResult", false, "Nat");
    let mut s = Store::new();
    let u = rock::type0(&mut s);
    let prev = v(&mut s, 0);
    let bool_ = bool_def(&mut s);
    let field = v(&mut s, 0);
    let good = data(
        &mut s,
        vec![],
        vec![u, prev],
        vec![ctor(vec![bool_], vec![false], vec![bool_, field])],
    );
    infer(&mut s, Ctx::empty(), good).unwrap();
    let f = con(&mut s, bool_, 1, vec![]);
    let term = con(&mut s, good, 0, vec![f]);
    let expected = app(&mut s, good, &[bool_, f]);
    let ty = nbe::eval(&mut s, None, expected);
    check(&mut s, Ctx::empty(), term, ty).unwrap();
    let inferred = infer(&mut s, Ctx::empty(), term).unwrap();
    assert!(nbe::conv(&mut s, 0, inferred, ty));
    let nat = rock::nat_def(&mut s);
    let bad = data(
        &mut s,
        vec![],
        vec![u, prev],
        vec![ctor(vec![bool_], vec![false], vec![nat, field])],
    );
    assert!(infer(&mut s, Ctx::empty(), bad).is_err());
}

#[test]
fn missing_and_extra_result_indices_rejected() {
    for count in [0, 2] {
        let mut s = Store::new();
        let bool_ = bool_def(&mut s);
        let t = con(&mut s, bool_, 0, vec![]);
        let def = data(
            &mut s,
            vec![],
            vec![bool_],
            vec![ctor(vec![], vec![], vec![t; count])],
        );
        assert_eq!(
            infer(&mut s, Ctx::empty(), def),
            Err(TypeError::ConstructorArity {
                expected: 1,
                found: count
            })
        );
    }
}

#[test]
fn malformed_signature_rejected_through_constructor_apis() {
    let mut s = Store::new();
    let free = v(&mut s, 0);
    let def = data(
        &mut s,
        vec![],
        vec![free],
        vec![ctor(vec![], vec![], vec![free])],
    );
    let term = con(&mut s, def, 0, vec![]);
    assert!(matches!(
        infer(&mut s, Ctx::empty(), term),
        Err(TypeError::UnboundVariable { .. })
    ));
    let bool_ = bool_def(&mut s);
    let b = nbe::eval(&mut s, None, bool_);
    let ty = s.values.alloc(Value::Inductive { def, args: vec![b] });
    assert!(matches!(
        check(&mut s, Ctx::empty(), term, ty),
        Err(TypeError::UnboundVariable { .. })
    ));
}

fn chain(s: &mut Store) -> (TermId, TermId, TermId, TermId) {
    let nat = rock::nat_def(s);
    let z = rock::nat_zero(s, nat);
    let self_ = v(s, 2);
    let n = v(s, 0);
    let child = app(s, self_, &[n]);
    let n = v(s, 1);
    let next = rock::nat_suc(s, nat, n);
    let def = data(
        s,
        vec![],
        vec![nat],
        vec![
            ctor(vec![], vec![], vec![z]),
            ctor(vec![nat, child], vec![false, true], vec![next]),
        ],
    );
    infer(s, Ctx::empty(), def).unwrap();
    let base = con(s, def, 0, vec![]);
    (def, nat, z, base)
}
#[test]
fn indexed_recursive_case_uses_child_index_and_fixed_parameters() {
    reference::assert_agda("IndexedScopes", true, "");
    let mut s = Store::new();
    let (def, nat, z, base) = chain(&mut s);
    let one = rock::nat_suc(&mut s, nat, z);
    let l1 = con(&mut s, def, 1, vec![z, base]);
    let l2 = con(&mut s, def, 1, vec![one, l1]);
    let motive = s.terms.alloc(Term::Lam(nat));
    let ih = v(&mut s, 0);
    let mut step = rock::nat_suc(&mut s, nat, ih);
    for _ in 0..3 {
        step = s.terms.alloc(Term::Lam(step));
    }
    let case = s.terms.alloc(Term::Case {
        target: l2,
        motive,
        branches: vec![z, step],
    });
    let ty = infer(&mut s, Ctx::empty(), case).unwrap();
    let nat_ty = nbe::eval(&mut s, None, nat);
    assert!(nbe::conv(&mut s, 0, ty, nat_ty));
    let nf = normalize(&mut s, case);
    let nf = nbe::eval(&mut s, None, nf);
    let two = rock::nat_suc(&mut s, nat, one);
    let two = nbe::eval(&mut s, None, two);
    assert!(nbe::conv(&mut s, 0, nf, two));
}
#[test]
fn indexed_motive_cannot_be_specialized_to_target_fiber() {
    reference::assert_agda("IndexedBadMotive", false, "zero");
    let mut s = Store::new();
    let (def, _, z, base) = chain(&mut s);
    let dz = app(&mut s, def, &[z]);
    let u = rock::type0(&mut s);
    let f_ty = s.terms.alloc(Term::Pi(dz, u));
    let f_ty = nbe::eval(&mut s, None, f_ty);
    let ctx = Ctx::empty().bind(&mut s, f_ty);
    let motive = v(&mut s, 0);
    let case = s.terms.alloc(Term::Case {
        target: base,
        motive,
        branches: vec![],
    });
    // Rejected at motive generalization, before branch arity checking.
    assert_eq!(infer(&mut s, ctx, case), Err(TypeError::ConversionFailure));
}
#[test]
fn formal_indices_must_be_explicit_constructor_fields() {
    let mut s = Store::new();
    let nat = rock::nat_def(&mut s);
    let formal = v(&mut s, 0);
    let def = data(
        &mut s,
        vec![],
        vec![nat],
        vec![ctor(vec![], vec![], vec![formal])],
    );
    assert_eq!(
        infer(&mut s, Ctx::empty(), def),
        Err(TypeError::UnsupportedIndexDependency)
    );
}

#[test]
fn explicit_function_index_is_checked_before_evaluation() {
    let mut s = Store::new();
    let nat = rock::nat_def(&mut s);
    let fn_ty = s.terms.alloc(Term::Pi(nat, nat));
    let x = v(&mut s, 0);
    let id = s.terms.alloc(Term::Lam(x));
    let def = data(
        &mut s,
        vec![],
        vec![fn_ty],
        vec![ctor(vec![], vec![], vec![id])],
    );
    infer(&mut s, Ctx::empty(), def).unwrap();
    let annotated_id = s.terms.alloc(Term::Ann(id, fn_ty));
    let ty = app(&mut s, def, &[annotated_id]);
    infer(&mut s, Ctx::empty(), ty).unwrap();
    let ty = nbe::eval(&mut s, None, ty);
    let good = s.terms.alloc(Term::Con {
        def,
        idx: 0,
        args: vec![],
        indices: vec![id],
    });
    check(&mut s, Ctx::empty(), good, ty).unwrap();
    infer(&mut s, Ctx::empty(), good).unwrap();
    let bad = s.terms.alloc(Term::Con {
        def,
        idx: 0,
        args: vec![],
        indices: vec![x],
    });
    assert!(matches!(
        check(&mut s, Ctx::empty(), bad, ty),
        Err(TypeError::UnboundVariable { .. })
    ));
    assert!(matches!(
        infer(&mut s, Ctx::empty(), bad),
        Err(TypeError::UnboundVariable { .. })
    ));
}
