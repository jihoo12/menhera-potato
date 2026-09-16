//! Adversarial specifications, deliberately allowed to fail during the audit.
//! No panic counts as rejection. Positive cases independently probe evaluation
//! and checking so a checker panic cannot conceal a runtime ordering result.
#[path = "differential/branch_reference.rs"]
mod branch_reference;

use std::panic::{AssertUnwindSafe, catch_unwind};

use rock::nbe::{self, Store};
use rock::{
    ConstructorDef, Ctx, Term, TermId, check, infer, nat_def, nat_suc, nat_zero, normalize, type0,
};

fn probe<T: std::fmt::Debug>(f: impl FnOnce() -> T) -> Result<T, String> {
    catch_unwind(AssertUnwindSafe(f)).map_err(|p| {
        p.downcast_ref::<String>()
            .cloned()
            .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_else(|| "non-string panic".into())
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
fn ctor(
    name: &str,
    arg_types: Vec<TermId>,
    recursive: Vec<bool>,
    indices: Vec<TermId>,
) -> ConstructorDef {
    ConstructorDef {
        name: name.into(),
        arg_types,
        recursive,
        indices,
    }
}
fn data(
    s: &mut Store,
    params: Vec<TermId>,
    indices: Vec<TermId>,
    constructors: Vec<ConstructorDef>,
) -> TermId {
    let level = s.levels.alloc(rock::Level::Zero);
    s.terms.alloc(Term::Inductive {
        level,
        params,
        indices,
        constructors,
    })
}
fn bool_def(s: &mut Store) -> TermId {
    data(
        s,
        vec![],
        vec![],
        vec![
            ctor("true", vec![], vec![], vec![]),
            ctor("false", vec![], vec![], vec![]),
        ],
    )
}
fn var(s: &mut Store, i: u32) -> TermId {
    s.terms.alloc(Term::Var(i))
}
fn lams(s: &mut Store, n: usize, mut body: TermId) -> TermId {
    for _ in 0..n {
        body = s.terms.alloc(Term::Lam(body));
    }
    body
}
fn numeral(s: &mut Store, nat: TermId, n: u32) -> TermId {
    let mut t = nat_zero(s, nat);
    for _ in 0..n {
        t = nat_suc(s, nat, t);
    }
    t
}
fn read_nat(s: &Store, nat: TermId, mut t: TermId) -> u32 {
    let mut n = 0;
    loop {
        match s.terms.get(t) {
            Term::Con {
                def, idx: 0, args, ..
            } if *def == nat && args.is_empty() => return n,
            Term::Con {
                def, idx: 1, args, ..
            } if *def == nat && args.len() == 1 => {
                n += 1;
                t = args[0];
            }
            other => panic!("noncanonical Nat: {other:?}"),
        }
    }
}
fn reject(s: &mut Store, t: TermId) {
    let result = probe(|| infer(s, Ctx::empty(), t));
    assert!(
        matches!(result, Ok(Err(_))),
        "expected TypeError, not acceptance or panic: {result:?}"
    );
}
fn accepted_nf(s: &mut Store, t: TermId, expected: TermId) {
    let runtime = probe(|| {
        let nf = normalize(s, t);
        let a = nbe::eval(s, None, nf);
        let b = nbe::eval(s, None, expected);
        assert!(
            nbe::conv(s, 0, a, b),
            "unexpected normal form: {:?}",
            s.terms.get(nf)
        );
    });
    let typing = probe(|| infer(s, Ctx::empty(), t));
    assert!(
        runtime.is_ok() && matches!(typing, Ok(Ok(_))),
        "runtime={runtime:?}; typing={typing:?}"
    );
}

struct Tree {
    nat: TermId,
    bool_: TermId,
    def: TermId,
    leaf: TermId,
    result: TermId,
}
impl Tree {
    fn new(s: &mut Store) -> Self {
        let nat = nat_def(s);
        let bool_ = bool_def(s);
        // node fields: Nat, Tree, Bool, Tree. Self is Var(k) in field k.
        let left = var(s, 1);
        let right = var(s, 3);
        let def = data(
            s,
            vec![],
            vec![],
            vec![
                ctor("leaf", vec![], vec![], vec![]),
                ctor(
                    "node",
                    vec![nat, left, bool_, right],
                    vec![false, true, false, true],
                    vec![],
                ),
            ],
        );
        infer(s, Ctx::empty(), def).expect("Tree fixture formation");
        let leaf = con(s, def, 0, vec![]);
        let result = s.terms.alloc(Term::Sigma(nat, nat));
        Self {
            nat,
            bool_,
            def,
            leaf,
            result,
        }
    }
    fn node(&self, s: &mut Store, n: u32, left: TermId, flag: bool, right: TermId) -> TermId {
        let n = numeral(s, self.nat, n);
        let b = con(s, self.bool_, usize::from(!flag), vec![]);
        con(s, self.def, 1, vec![n, left, b, right])
    }
    // `order` names slots: 0=n, 1=left, 2=IH-left, 3=b, 4=right, 5=IH-right.
    // All domains are closed. Ann makes every assumed slot type explicit, even
    // the Tree fields, which are not used by the numeric result computation.
    fn branch(&self, s: &mut Store, order: [usize; 6]) -> TermId {
        let slot = |id| (5 - order.iter().position(|&x| x == id).unwrap()) as u32;
        let n = var(s, slot(0));
        let ih_l = var(s, slot(2));
        let ih_r = var(s, slot(5));
        let b = var(s, slot(3));
        let seed = s.terms.alloc(Term::Pair(n, n));
        let l = s.terms.alloc(Term::Fst(ih_l));
        let r = s.terms.alloc(Term::Snd(ih_r));
        let combine = s.terms.alloc(Term::Pair(l, r));
        let motive = s.terms.alloc(Term::Lam(self.result));
        let body = s.terms.alloc(Term::Case {
            target: b,
            motive,
            branches: vec![seed, combine],
        });
        let body = lams(s, 6, body);
        let domains = [
            self.nat,
            self.def,
            self.result,
            self.bool_,
            self.def,
            self.result,
        ];
        let mut ty = self.result;
        for &slot in order.iter().rev() {
            ty = s.terms.alloc(Term::Pi(domains[slot], ty));
        }
        let branch = s.terms.alloc(Term::Ann(body, ty));
        infer(s, Ctx::empty(), branch).expect("branch independently inhabits its stated telescope");
        branch
    }
    fn case(&self, s: &mut Store, target: TermId, branch: TermId) -> TermId {
        let zero = nat_zero(s, self.nat);
        let base = s.terms.alloc(Term::Pair(zero, zero));
        let motive = s.terms.alloc(Term::Lam(self.result));
        s.terms.alloc(Term::Case {
            target,
            motive,
            branches: vec![base, branch],
        })
    }
    fn example(&self, s: &mut Store, swapped: bool) -> TermId {
        let l = self.node(s, 2, self.leaf, true, self.leaf);
        let r = self.node(s, 5, self.leaf, true, self.leaf);
        if swapped {
            self.node(s, 7, r, false, l)
        } else {
            self.node(s, 7, l, false, r)
        }
    }
    fn assert_case(&self, s: &mut Store, case: TermId, expected: (u32, u32)) {
        let runtime = probe(|| {
            let nf = normalize(s, case);
            let Term::Pair(a, b) = *s.terms.get(nf) else {
                panic!("expected canonical pair")
            };
            assert_eq!(
                (read_nat(s, self.nat, a), read_nat(s, self.nat, b)),
                expected
            );
        });
        let typing = probe(|| {
            let ty = infer(s, Ctx::empty(), case)?;
            let expected_ty = nbe::eval(s, None, self.result);
            assert!(
                nbe::conv(s, 0, ty, expected_ty),
                "Case inferred the wrong result type"
            );
            Ok::<_, rock::TypeError>(ty)
        });
        assert!(
            runtime.is_ok() && matches!(typing, Ok(Ok(_))),
            "runtime={runtime:?}; typing={typing:?}"
        );
    }
}

#[test]
fn a1_interleaved_branch_typechecks_and_normalizes() {
    branch_reference::assert_agda("BranchTelescope", true, "");
    let mut s = Store::new();
    let f = Tree::new(&mut s);
    let branch = f.branch(&mut s, [0, 1, 2, 3, 4, 5]);
    let target = f.example(&mut s, false);
    let case = f.case(&mut s, target, branch);
    f.assert_case(&mut s, case, (2, 5));
}
#[test]
fn a2_swapped_recursive_argument_and_ih_rejected() {
    branch_reference::assert_agda("BranchSwapChild", false, "Tree");
    let mut s = Store::new();
    let f = Tree::new(&mut s);
    let branch = f.branch(&mut s, [0, 2, 1, 3, 4, 5]);
    let target = f.example(&mut s, false);
    let case = f.case(&mut s, target, branch);
    reject(&mut s, case);
}
#[test]
fn a3_swapped_bool_and_ih_rejected() {
    branch_reference::assert_agda("BranchSwapBool", false, "Bool");
    let mut s = Store::new();
    let f = Tree::new(&mut s);
    let branch = f.branch(&mut s, [0, 1, 3, 2, 4, 5]);
    let target = f.example(&mut s, false);
    let case = f.case(&mut s, target, branch);
    reject(&mut s, case);
}
#[test]
fn a4_distinct_ihs_follow_swapped_subtrees() {
    branch_reference::assert_agda("BranchTelescope", true, "");
    let mut s = Store::new();
    let f = Tree::new(&mut s);
    let branch = f.branch(&mut s, [0, 1, 2, 3, 4, 5]);
    let target = f.example(&mut s, true);
    let case = f.case(&mut s, target, branch);
    f.assert_case(&mut s, case, (5, 2));
}

// B uses a binary Fork to avoid the mixed-field subtraction underflow masking
// every dependent test. Q : Fork -> Type is an empty indexed family, and
// P(t) = Q(t) -> Q(t). P(left) and P(right) differ for distinct neutral children;
// nevertheless identity inhabits P(t) for every t (no empty inhabitant needed).
fn fork(s: &mut Store) -> (TermId, TermId, TermId) {
    let a = var(s, 0);
    let b = var(s, 1);
    let def = data(
        s,
        vec![],
        vec![],
        vec![
            ctor("leaf", vec![], vec![], vec![]),
            ctor("fork", vec![a, b], vec![true, true], vec![]),
        ],
    );
    infer(s, Ctx::empty(), def).unwrap();
    let leaf = con(s, def, 0, vec![]);
    let q = data(s, vec![], vec![def], vec![]);
    infer(s, Ctx::empty(), q).unwrap();
    (def, leaf, q)
}
fn p_var(s: &mut Store, q: TermId, child: u32) -> TermId {
    let t = var(s, child);
    let qt = s.terms.alloc(Term::App(q, t));
    let t1 = var(s, child + 1);
    let qt1 = s.terms.alloc(Term::App(q, t1));
    s.terms.alloc(Term::Pi(qt, qt1))
}
fn p_node(s: &mut Store, q: TermId, def: TermId, offset: u32) -> TermId {
    // Under the four runtime binders: left=3, IH-left=2, right=1, IH-right=0.
    let l = var(s, 3 + offset);
    let r = var(s, 1 + offset);
    let t = con(s, def, 1, vec![l, r]);
    let qt = s.terms.alloc(Term::App(q, t));
    let l = var(s, 4 + offset);
    let r = var(s, 2 + offset);
    let t = con(s, def, 1, vec![l, r]);
    let qt1 = s.terms.alloc(Term::App(q, t));
    s.terms.alloc(Term::Pi(qt, qt1))
}
fn dependent_case(s: &mut Store, wrong_child: bool) -> (TermId, TermId) {
    let (def, leaf, q) = fork(s);
    let x = var(s, 0);
    let id = s.terms.alloc(Term::Lam(x));
    let p = p_var(s, q, 0);
    let motive = s.terms.alloc(Term::Lam(p));
    let pchild = p_var(s, q, if wrong_child { 1 } else { 3 });
    let ih = var(s, 2);
    let ih = s.terms.alloc(Term::Ann(ih, pchild));
    // (lambda (_ : P(child)). identity) IH-left : P(fork left right).
    let pnode_shifted = p_node(s, q, def, 1);
    let discard_ty = s.terms.alloc(Term::Pi(pchild, pnode_shifted));
    let discard = s.terms.alloc(Term::Lam(id));
    let discard = s.terms.alloc(Term::Ann(discard, discard_ty));
    let body = s.terms.alloc(Term::App(discard, ih));
    let branch = lams(s, 4, body);
    let target = con(s, def, 1, vec![leaf, leaf]);
    let case = s.terms.alloc(Term::Case {
        target,
        motive,
        branches: vec![id, branch],
    });
    (case, id)
}
#[test]
fn b1_dependent_ih_for_correct_child_accepted() {
    branch_reference::assert_agda("BranchTelescope", true, "");
    let mut s = Store::new();
    let (case, id) = dependent_case(&mut s, false);
    accepted_nf(&mut s, case, id);
}
#[test]
fn b2_left_ih_at_right_child_type_rejected() {
    branch_reference::assert_agda("BranchWrongChild", false, "expression il has type P r");
    let mut s = Store::new();
    let (case, _) = dependent_case(&mut s, true);
    reject(&mut s, case);
}
#[test]
fn b_control_child_specific_ih_types_are_distinct() {
    let mut s = Store::new();
    let (def, _, q) = fork(&mut s);
    let d = nbe::eval(&mut s, None, def);
    let ctx = Ctx::empty().bind(&mut s, d).bind(&mut s, d);
    let pl = p_var(&mut s, q, 1);
    let pr = p_var(&mut s, q, 0);
    let pl = nbe::eval(&mut s, ctx.env, pl);
    let pr = nbe::eval(&mut s, ctx.env, pr);
    assert!(!nbe::conv(&mut s, ctx.depth, pl, pr));
    let ctx = ctx.bind(&mut s, pl);
    let ih = var(&mut s, 0);
    check(&mut s, ctx, ih, pl).unwrap();
    assert!(check(&mut s, ctx, ih, pr).is_err());
}

// C: Tagged (A : Type) : Bool -> Type; tag : (b : Bool) -> A -> Tagged A b.
// Signature: parameter type Type in empty ctx, index type Bool under A.
// Body before fields: A=0, formal Bool index=1, self=2.
// Field a after b: b=0, A=1, formal index=2, self=3.
// Result after b,a: a=0, b=1, A=2, formal index=3, self=4.
fn tagged(s: &mut Store, param_ref: u32, result_ref: u32) -> (TermId, TermId) {
    let bool_ = bool_def(s);
    let universe = type0(s);
    let a = var(s, param_ref);
    let idx = var(s, result_ref);
    let def = data(
        s,
        vec![universe],
        vec![bool_],
        vec![ctor("tag", vec![bool_, a], vec![false, false], vec![idx])],
    );
    (def, bool_)
}
fn tagged_type(s: &mut Store, def: TermId, a: TermId, b: TermId) -> TermId {
    let da = s.terms.alloc(Term::App(def, a));
    s.terms.alloc(Term::App(da, b))
}
#[test]
fn c1_parameter_visible_in_constructor_field() {
    let mut s = Store::new();
    let (def, _) = tagged(&mut s, 1, 1);
    infer(&mut s, Ctx::empty(), def).expect("A is Var(1) after b");
}
#[test]
fn c1_constructor_use_preserves_parameter_and_index() {
    let mut s = Store::new();
    let (def, bool_) = tagged(&mut s, 1, 1);
    infer(&mut s, Ctx::empty(), def).unwrap();
    let nat = nat_def(&mut s);
    let two = numeral(&mut s, nat, 2);
    let b = con(&mut s, bool_, 0, vec![]);
    let ty = tagged_type(&mut s, def, nat, b);
    infer(&mut s, Ctx::empty(), ty).unwrap();
    let value = nbe::eval(&mut s, None, ty);
    let term = con(&mut s, def, 0, vec![b, two]);
    check(&mut s, Ctx::empty(), term, value).unwrap();
    let annotated = s.terms.alloc(Term::Ann(term, ty));
    accepted_nf(&mut s, annotated, term);
}
#[test]
fn c2_shifted_parameter_reference_rejected() {
    let mut s = Store::new();
    let (def, _) = tagged(&mut s, 2, 1);
    reject(&mut s, def); // Var(2) is a Bool value, not A : Type.
}
#[test]
fn c3_result_index_uses_constructor_argument_scope() {
    let mut s = Store::new();
    let (def, bool_) = tagged(&mut s, 1, 1);
    infer(&mut s, Ctx::empty(), def).unwrap();
    let nat = nat_def(&mut s);
    let z = nat_zero(&mut s, nat);
    for idx in [0, 1] {
        let b = con(&mut s, bool_, idx, vec![]);
        let ty = tagged_type(&mut s, def, nat, b);
        let term = s.terms.alloc(Term::Con {
            def,
            idx: 0,
            args: vec![b, z],
            indices: vec![b],
        });
        let annotated = s.terms.alloc(Term::Ann(term, ty));
        // Both Bool values must agree with the result expression Var(1),
        // including when the caller supplies an explicit index.
        accepted_nf(&mut s, annotated, term);
    }
}

#[test]
fn c3_off_by_one_result_index_rejected_at_formation() {
    branch_reference::assert_agda("IndexedBadResult", false, "Bool");
    let mut s = Store::new();
    let (def, _) = tagged(&mut s, 1, 0);
    reject(&mut s, def); // a : A cannot uniformly be used as a Bool index.
}
#[test]
fn c3_wrong_result_index_rejected_at_constructor_use() {
    let mut s = Store::new();
    let (def, bool_) = tagged(&mut s, 1, 1);
    infer(&mut s, Ctx::empty(), def).unwrap();
    let nat = nat_def(&mut s);
    let z = nat_zero(&mut s, nat);
    let t = con(&mut s, bool_, 0, vec![]);
    let f = con(&mut s, bool_, 1, vec![]);
    let ty = tagged_type(&mut s, def, nat, f);
    let ty = nbe::eval(&mut s, None, ty);
    let term = con(&mut s, def, 0, vec![t, z]);
    assert!(check(&mut s, Ctx::empty(), term, ty).is_err());
}
#[test]
fn c4_parameter_type_cannot_capture_later_index_binder() {
    branch_reference::assert_agda("IndexedBadScope", false, "Not in scope");
    let mut s = Store::new();
    // Invalid signature: the first parameter's type is Var(0) in empty ctx.
    // Only the reversed body context would make that reference a bound Type.
    let p = var(&mut s, 0);
    let u = type0(&mut s);
    let def = data(&mut s, vec![p], vec![u], vec![]);
    reject(&mut s, def);
}
#[test]
fn c4_dependent_index_type_sees_earlier_parameter() {
    branch_reference::assert_agda("IndexedScopes", true, "");
    let mut s = Store::new();
    let u = type0(&mut s);
    let a = var(&mut s, 0);
    // Valid signature: (A : Type) -> A -> Type. In index type, A is Var(0).
    let def = data(&mut s, vec![u], vec![a], vec![]);
    infer(&mut s, Ctx::empty(), def).expect("index type sees earlier parameter A");
}
#[test]
fn c_case_motive_and_constructor_scopes_agree() {
    branch_reference::assert_agda("IndexedScopes", true, "");
    let mut s = Store::new();
    let (def, bool_) = tagged(&mut s, 1, 1);
    infer(&mut s, Ctx::empty(), def).unwrap();
    let nat = nat_def(&mut s);
    let z = nat_zero(&mut s, nat);
    let b = con(&mut s, bool_, 0, vec![]);
    let ty = tagged_type(&mut s, def, nat, b);
    let target = con(&mut s, def, 0, vec![b, z]);
    let target = s.terms.alloc(Term::Ann(target, ty));
    let motive = s.terms.alloc(Term::Lam(nat));
    let branch = lams(&mut s, 2, z);
    let case = s.terms.alloc(Term::Case {
        target,
        motive,
        branches: vec![branch],
    });
    accepted_nf(&mut s, case, z);
}

#[test]
fn e1_missing_recursive_ih_binder_rejected() {
    let mut s = Store::new();
    let nat = nat_def(&mut s);
    let z = nat_zero(&mut s, nat);
    let target = nat_suc(&mut s, nat, z);
    let motive = s.terms.alloc(Term::Lam(nat));
    let branch = lams(&mut s, 1, z); // child present, required IH missing
    let case = s.terms.alloc(Term::Case {
        target,
        motive,
        branches: vec![z, branch],
    });
    reject(&mut s, case);
}
#[test]
fn e2_nonrecursive_field_cannot_receive_extra_ih() {
    let mut s = Store::new();
    let nat = nat_def(&mut s);
    let z = nat_zero(&mut s, nat);
    let def = data(
        &mut s,
        vec![],
        vec![],
        vec![ctor("box", vec![nat], vec![false], vec![])],
    );
    infer(&mut s, Ctx::empty(), def).unwrap();
    let target = con(&mut s, def, 0, vec![z]);
    let motive = s.terms.alloc(Term::Lam(nat));
    let branch = lams(&mut s, 2, z); // one field, no IH
    let case = s.terms.alloc(Term::Case {
        target,
        motive,
        branches: vec![branch],
    });
    reject(&mut s, case);
}
#[test]
fn e3_two_recursive_fields_require_four_branch_binders() {
    branch_reference::assert_agda("BranchMissingIH", false, "Nat");
    let mut s = Store::new();
    let (def, leaf, _) = fork(&mut s);
    let nat = nat_def(&mut s);
    let z = nat_zero(&mut s, nat);
    let target = con(&mut s, def, 1, vec![leaf, leaf]);
    let motive = s.terms.alloc(Term::Lam(nat));
    let branch = lams(&mut s, 3, z); // correct branch count, incorrect field+IH count
    let case = s.terms.alloc(Term::Case {
        target,
        motive,
        branches: vec![z, branch],
    });
    reject(&mut s, case);
}

#[test]
fn constructor_open_fields_keep_caller_scope_in_check_and_infer() {
    let mut s = Store::new();
    let (def, _, _) = fork(&mut s);
    let nat = nat_def(&mut s);
    let tree_ty = nbe::eval(&mut s, None, def);
    let ih_ty = nbe::eval(&mut s, None, nat);
    // Caller binders: left, IH-left, right, IH-right. Constructor syntax
    // supplies only left and right; checking either must not add a binder.
    let ctx = Ctx::empty()
        .bind(&mut s, tree_ty)
        .bind(&mut s, ih_ty)
        .bind(&mut s, tree_ty)
        .bind(&mut s, ih_ty);
    let left = var(&mut s, 3);
    let right = var(&mut s, 1);
    let ih = var(&mut s, 0);
    let good = con(&mut s, def, 1, vec![left, right]);
    check(&mut s, ctx, good, tree_ty).unwrap();
    let inferred = infer(&mut s, ctx, good).unwrap();
    assert!(nbe::conv(&mut s, ctx.depth, inferred, tree_ty));
    let bad = con(&mut s, def, 1, vec![left, ih]);
    assert!(check(&mut s, ctx, bad, tree_ty).is_err());
    assert!(infer(&mut s, ctx, bad).is_err());
}

#[test]
fn constructor_dependent_field_uses_previous_value_not_new_source_binder() {
    let mut s = Store::new();
    let u = type0(&mut s);
    let previous_a = var(&mut s, 0);
    let level = s.levels.alloc(rock::Level::Zero);
    let level = s.levels.alloc(rock::Level::Suc(level));
    // Pack : Type1; pack : (A : Type0) -> A -> Pack.
    let def = s.terms.alloc(Term::Inductive {
        level,
        params: vec![],
        indices: vec![],
        constructors: vec![ctor(
            "pack",
            vec![u, previous_a],
            vec![false, false],
            vec![],
        )],
    });
    infer(&mut s, Ctx::empty(), def).unwrap();
    let u_val = nbe::eval(&mut s, None, u);
    let ctx = Ctx::empty().bind(&mut s, u_val);
    let a = var(&mut s, 0);
    let a_val = nbe::eval(&mut s, ctx.env, a);
    let ctx = ctx.bind(&mut s, a_val);
    // Under A,x: field 0 is Var(1); field 1 is Var(0).
    // The stored second field TYPE is also Var(0), but means the supplied A.
    let a = var(&mut s, 1);
    let x = var(&mut s, 0);
    let term = con(&mut s, def, 0, vec![a, x]);
    let ty = nbe::eval(&mut s, ctx.env, def);
    check(&mut s, ctx, term, ty).unwrap();
    let inferred = infer(&mut s, ctx, term).unwrap();
    assert!(nbe::conv(&mut s, ctx.depth, inferred, ty));
    let bad = con(&mut s, def, 0, vec![a, a]);
    assert!(check(&mut s, ctx, bad, ty).is_err());
    assert!(infer(&mut s, ctx, bad).is_err());
}
