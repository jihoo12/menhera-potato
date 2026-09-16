//! Focused dependent-inductive telescope review. All typing probes start with
//! closed syntax at Ctx::empty(); no semantic contexts or values are fabricated.
#[path = "differential/branch_reference.rs"]
mod reference;

use rock::{ConstructorDef, Ctx, Level, Store, Term, TermId, TypeError, infer, nbe};

fn v(s: &mut Store, i: u32) -> TermId {
    s.terms.alloc(Term::Var(i))
}
fn app(s: &mut Store, mut f: TermId, xs: &[TermId]) -> TermId {
    for &x in xs {
        f = s.terms.alloc(Term::App(f, x));
    }
    f
}
fn lams(s: &mut Store, count: usize, mut body: TermId) -> TermId {
    for _ in 0..count {
        body = s.terms.alloc(Term::Lam(body));
    }
    body
}
fn ctor(fields: Vec<TermId>, flags: Vec<bool>, indices: Vec<TermId>) -> ConstructorDef {
    ConstructorDef {
        name: "c".into(),
        arg_types: fields,
        recursive: flags,
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
    s.terms.alloc(Term::Inductive {
        level,
        params,
        indices,
        constructors: cs,
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

#[test]
fn negative_self_occurrence_in_constructor_result_is_rejected() {
    reference::assert_agda("ResultIndexNegative", false, "not strictly positive");
    let mut s = Store::new();
    let empty = data(&mut s, vec![], vec![], vec![]);
    let u = rock::type0(&mut s);
    // D : Type0 -> Type0; c : D (D Empty -> Empty).
    // Result syntax sees [self, formal-index]; self = Var(1).
    let self_ = v(&mut s, 1);
    let d_empty = app(&mut s, self_, &[empty]);
    let negative = s.terms.alloc(Term::Pi(d_empty, empty));
    let d = data(
        &mut s,
        vec![],
        vec![u],
        vec![ctor(vec![], vec![], vec![negative])],
    );
    assert!(
        infer(&mut s, Ctx::empty(), d).is_err(),
        "accepted a negative occurrence of D in its result index"
    );
}

#[test]
fn self_free_function_result_index_is_supported() {
    reference::assert_agda("ResultIndexPositive", true, "");
    let mut s = Store::new();
    let empty = data(&mut s, vec![], vec![], vec![]);
    let nat = rock::nat_def(&mut s);
    let u = rock::type0(&mut s);
    let index = s.terms.alloc(Term::Pi(nat, empty));
    let d = data(
        &mut s,
        vec![],
        vec![u],
        vec![ctor(vec![], vec![], vec![index])],
    );
    infer(&mut s, Ctx::empty(), d).unwrap();
    let c = con(&mut s, d, 0, vec![]);
    infer(&mut s, Ctx::empty(), c).unwrap();
}

// D (A : Type0) (B : A -> Type0) : (a : A) -> B a -> Type0
// leaf : (x : A) (y : B x) -> D A B x y
// step : (x : A) (y : B x) (r : D A B x y)
//        (z : B x) (s : D A B x z) -> D A B x z
// Runtime branch: x, y, r, IH-r, z, s, IH-s.
struct Telescope {
    d: TermId,
    nat: TermId,
    tag: TermId,
    zero: TermId,
}
impl Telescope {
    fn new(s: &mut Store) -> Self {
        let nat = rock::nat_def(s);
        let zero = rock::nat_zero(s, nat);
        let n = v(s, 0);
        let tag = data(
            s,
            vec![],
            vec![nat],
            vec![
                ctor(vec![nat], vec![false], vec![n]),
                ctor(vec![nat], vec![false], vec![n]),
            ],
        );
        let u = rock::type0(s);
        let a = v(s, 0);
        let b_ty = s.terms.alloc(Term::Pi(a, u));
        let a_index = v(s, 1);
        let b = v(s, 1);
        let a = v(s, 0);
        let b_index = app(s, b, &[a]);
        // Body base [self, a, b, A, B].
        let x_ty = v(s, 1);
        let b = v(s, 1);
        let x = v(s, 0);
        let y_ty = app(s, b, &[x]);
        let self_ = v(s, 6);
        let a = v(s, 3);
        let b = v(s, 2);
        let x = v(s, 1);
        let y = v(s, 0);
        let r_ty = app(s, self_, &[a, b, x, y]);
        let b = v(s, 3);
        let x = v(s, 2);
        let z_ty = app(s, b, &[x]);
        let self_ = v(s, 8);
        let a = v(s, 5);
        let b = v(s, 4);
        let x = v(s, 3);
        let z = v(s, 0);
        let s_ty = app(s, self_, &[a, b, x, z]);
        let lx = v(s, 1);
        let ly = v(s, 0);
        let sx = v(s, 4);
        let sz = v(s, 1);
        let d = data(
            s,
            vec![u, b_ty],
            vec![a_index, b_index],
            vec![
                ctor(vec![x_ty, y_ty], vec![false, false], vec![lx, ly]),
                ctor(
                    vec![x_ty, y_ty, r_ty, z_ty, s_ty],
                    vec![false, false, true, false, true],
                    vec![sx, sz],
                ),
            ],
        );
        infer(s, Ctx::empty(), d).expect("two dependent parameters/indices form a family");
        Self { d, nat, tag, zero }
    }
    fn mark(&self, s: &mut Store, n: TermId, which: usize) -> TermId {
        con(s, self.tag, which, vec![n])
    }
    fn ty(&self, s: &mut Store, x: TermId, y: TermId) -> TermId {
        app(s, self.d, &[self.nat, self.tag, x, y])
    }
    fn leaf(&self, s: &mut Store, x: TermId, y: TermId) -> TermId {
        let c = con(s, self.d, 0, vec![x, y]);
        let ty = self.ty(s, x, y);
        s.terms.alloc(Term::Ann(c, ty))
    }
    fn step(
        &self,
        s: &mut Store,
        x: TermId,
        y: TermId,
        r: TermId,
        z: TermId,
        right: TermId,
    ) -> TermId {
        let c = con(s, self.d, 1, vec![x, y, r, z, right]);
        let ty = self.ty(s, x, z);
        s.terms.alloc(Term::Ann(c, ty))
    }
    fn fold(&self, s: &mut Store, target: TermId, select_right: bool) -> TermId {
        let motive = lams(s, 1, self.nat);
        let x = v(s, 1);
        let leaf = lams(s, 2, x);
        let ih = v(s, if select_right { 0 } else { 3 });
        let succ = rock::nat_suc(s, self.nat, ih);
        let step = lams(s, 7, succ);
        s.terms.alloc(Term::Case {
            target,
            motive,
            branches: vec![leaf, step],
        })
    }
    fn example(&self, s: &mut Store) -> (TermId, TermId, TermId) {
        let y = self.mark(s, self.zero, 0);
        let z = self.mark(s, self.zero, 1);
        let left = self.leaf(s, self.zero, y);
        let right_leaf = self.leaf(s, self.zero, z);
        let right = self.step(s, self.zero, z, right_leaf, z, right_leaf);
        let root = self.step(s, self.zero, y, left, z, right);
        (root, left, right)
    }
}
fn assert_nf(s: &mut Store, tm: TermId, expected: TermId) {
    let ty = infer(s, Ctx::empty(), tm).expect("closed test term typechecks");
    let value = nbe::eval(s, None, tm);
    let quoted = nbe::quote(s, 0, value);
    rock::check(s, Ctx::empty(), quoted, ty).expect("normal form preserves type");
    let qv = nbe::eval(s, None, quoted);
    let ev = nbe::eval(s, None, expected);
    assert!(nbe::conv(s, 0, value, qv));
    assert!(nbe::conv(s, 0, value, ev));
}

#[test]
fn dependent_telescopes_compute_each_child_ih_at_its_own_index() {
    let mut s = Store::new();
    let f = Telescope::new(&mut s);
    let (target, _, _) = f.example(&mut s);
    infer(&mut s, Ctx::empty(), target).unwrap();
    for (right, count) in [(false, 1), (true, 2)] {
        let case = f.fold(&mut s, target, right);
        let mut expected = f.zero;
        for _ in 0..count {
            expected = rock::nat_suc(&mut s, f.nat, expected);
        }
        assert_nf(&mut s, case, expected);
    }
}

#[test]
fn constructor_rejects_wrong_dependent_field_and_recursive_child_fiber() {
    let mut s = Store::new();
    let f = Telescope::new(&mut s);
    let (_, left, right) = f.example(&mut s);
    let y = f.mark(&mut s, f.zero, 0);
    let z = f.mark(&mut s, f.zero, 1);
    // Left expects D zero (tag0 zero); right inhabits D zero (tag1 zero).
    let bad = f.step(&mut s, f.zero, y, right, z, right);
    assert!(infer(&mut s, Ctx::empty(), bad).is_err());
    let one = rock::nat_suc(&mut s, f.nat, f.zero);
    let wrong_z = f.mark(&mut s, one, 1); // Tag one, not Tag zero
    let bad = f.step(&mut s, f.zero, y, left, wrong_z, right);
    assert!(infer(&mut s, Ctx::empty(), bad).is_err());
    let good = f.step(&mut s, f.zero, y, left, z, right);
    infer(&mut s, Ctx::empty(), good).unwrap();
}

#[test]
fn closed_lambda_preserves_caller_binders_across_constructor_instantiation() {
    let mut s = Store::new();
    let f = Telescope::new(&mut s);
    // lambda (x:Nat) (y:Tag x). leaf x y : (x:Nat) -> (y:Tag x) -> D Nat Tag x y
    let x = v(&mut s, 0);
    let y_ty = app(&mut s, f.tag, &[x]);
    let x = v(&mut s, 1);
    let y = v(&mut s, 0);
    let result = f.ty(&mut s, x, y);
    let rest = s.terms.alloc(Term::Pi(y_ty, result));
    let ty = s.terms.alloc(Term::Pi(f.nat, rest));
    let body = con(&mut s, f.d, 0, vec![x, y]);
    let body = lams(&mut s, 2, body);
    let ann = s.terms.alloc(Term::Ann(body, ty));
    infer(&mut s, Ctx::empty(), ann).unwrap();
    let y = f.mark(&mut s, f.zero, 0);
    let applied = app(&mut s, ann, &[f.zero, y]);
    let expected = f.leaf(&mut s, f.zero, y);
    assert_nf(&mut s, applied, expected);
}

impl Telescope {
    // P(t) = Q(fold t) -> Q(fold t). This is unary and uniform across
    // both indices, but distinguishes neutral children by their case spines.
    fn p(&self, s: &mut Store, q: TermId, t: TermId, weakened_t: TermId) -> TermId {
        let ft = self.fold(s, t, false);
        let a = app(s, q, &[ft]);
        let ft = self.fold(s, weakened_t, false);
        let b = app(s, q, &[ft]);
        s.terms.alloc(Term::Pi(a, b))
    }
    fn p_var(&self, s: &mut Store, q: TermId, i: u32) -> TermId {
        let t = v(s, i);
        let t1 = v(s, i + 1);
        self.p(s, q, t, t1)
    }
    fn parent(&self, s: &mut Store, offset: u32) -> TermId {
        let x = v(s, 6 + offset);
        let y = v(s, 5 + offset);
        let r = v(s, 4 + offset);
        let z = v(s, 2 + offset);
        let right = v(s, 1 + offset);
        self.step(s, x, y, r, z, right)
    }
    fn dependent_case(&self, s: &mut Store, wrong_child: bool) -> TermId {
        let q = data(s, vec![], vec![self.nat], vec![]);
        let p = self.p_var(s, q, 0);
        let motive = lams(s, 1, p);
        let x = v(s, 0);
        let id = lams(s, 1, x);
        let leaf = lams(s, 2, id);
        // r=4, IH-r=3, s=1 at the end of the step branch.
        let p_child = self.p_var(s, q, if wrong_child { 1 } else { 4 });
        let ih = v(s, 3);
        let ih = s.terms.alloc(Term::Ann(ih, p_child));
        let parent = self.parent(s, 1); // extra binder for discard
        let parent1 = self.parent(s, 2); // further binder inside P's Pi
        let p_parent = self.p(s, q, parent, parent1);
        let discard_ty = s.terms.alloc(Term::Pi(p_child, p_parent));
        let discard = lams(s, 1, id);
        let discard = s.terms.alloc(Term::Ann(discard, discard_ty));
        let body = app(s, discard, &[ih]);
        let step = lams(s, 7, body);
        let (target, _, _) = self.example(s);
        s.terms.alloc(Term::Case {
            target,
            motive,
            branches: vec![leaf, step],
        })
    }
}

#[test]
fn dependent_motive_ih_refers_to_exact_child_with_multiple_indices() {
    let mut s = Store::new();
    let f = Telescope::new(&mut s);
    let good = f.dependent_case(&mut s, false);
    let x = v(&mut s, 0);
    let id = lams(&mut s, 1, x);
    assert_nf(&mut s, good, id);
    let bad = f.dependent_case(&mut s, true);
    assert_eq!(
        infer(&mut s, Ctx::empty(), bad),
        Err(TypeError::ConversionFailure)
    );
}

#[test]
fn branch_field_after_ih_uses_original_field_not_ih() {
    for wrong in [false, true] {
        let mut s = Store::new();
        let f = Telescope::new(&mut s);
        // Manually specified telescope x,y,r,IH-r,z,s,IH-s.
        let x = v(&mut s, 0);
        let y_ty = app(&mut s, f.tag, &[x]);
        let x = v(&mut s, 1);
        let y = v(&mut s, 0);
        let r_ty = f.ty(&mut s, x, y);
        let x_for_z = v(&mut s, if wrong { 0 } else { 3 });
        let z_ty = app(&mut s, f.tag, &[x_for_z]);
        // In the wrong telescope z : Tag IH-r, make s use that same Nat
        // index, so the alternative branch type is independently well-formed.
        let x_for_s = v(&mut s, if wrong { 1 } else { 4 });
        let z = v(&mut s, 0);
        let s_ty = f.ty(&mut s, x_for_s, z);
        let mut branch_ty = f.nat;
        for domain in [f.nat, y_ty, r_ty, f.nat, z_ty, s_ty, f.nat]
            .into_iter()
            .rev()
        {
            branch_ty = s.terms.alloc(Term::Pi(domain, branch_ty));
        }
        let ih = v(&mut s, 3);
        let body = rock::nat_suc(&mut s, f.nat, ih);
        let branch = lams(&mut s, 7, body);
        let branch = s.terms.alloc(Term::Ann(branch, branch_ty));
        infer(&mut s, Ctx::empty(), branch).expect("alternate telescope must itself be well-typed");
        let x = v(&mut s, 1);
        let leaf = lams(&mut s, 2, x);
        let motive = lams(&mut s, 1, f.nat);
        let (target, _, _) = f.example(&mut s);
        let case = s.terms.alloc(Term::Case {
            target,
            motive,
            branches: vec![leaf, branch],
        });
        if wrong {
            assert_eq!(
                infer(&mut s, Ctx::empty(), case),
                Err(TypeError::ConversionFailure)
            );
        } else {
            let one = rock::nat_suc(&mut s, f.nat, f.zero);
            assert_nf(&mut s, case, one);
        }
    }
}

#[test]
fn motive_specialized_to_one_dependent_fiber_is_rejected() {
    let mut s = Store::new();
    let f = Telescope::new(&mut s);
    let (target, _, _) = f.example(&mut s);
    let z = f.mark(&mut s, f.zero, 1);
    let target_ty = f.ty(&mut s, f.zero, z);
    let u = rock::type0(&mut s);
    let h_ty = s.terms.alloc(Term::Pi(target_ty, u));
    let h = v(&mut s, 0);
    let case = s.terms.alloc(Term::Case {
        target,
        motive: h,
        branches: vec![],
    });
    let term = s.terms.alloc(Term::Pi(h_ty, case));
    // Inferring Pi checks the case before requiring its inferred type to be
    // a universe. Generic motive validation must fail before branch arity.
    assert_eq!(
        infer(&mut s, Ctx::empty(), term),
        Err(TypeError::ConversionFailure)
    );
}

#[test]
fn metadata_matches_exactly_the_two_direct_recursive_fields() {
    let mut s = Store::new();
    let f = Telescope::new(&mut s);
    for mask in 0..32 {
        let mut definition = s.terms.get(f.d).clone();
        if let Term::Inductive { constructors, .. } = &mut definition {
            constructors[1].recursive = (0..5).map(|k| mask & (1 << k) != 0).collect();
        }
        let d = s.terms.alloc(definition);
        let result = infer(&mut s, Ctx::empty(), d);
        if mask == (1 << 2) | (1 << 4) {
            assert!(result.is_ok());
        } else {
            assert_eq!(result, Err(TypeError::InvalidRecursiveMetadata));
        }
    }
    for length in [4, 6] {
        let mut definition = s.terms.get(f.d).clone();
        if let Term::Inductive { constructors, .. } = &mut definition {
            constructors[1].recursive.resize(length, false);
        }
        let d = s.terms.alloc(definition);
        assert_eq!(
            infer(&mut s, Ctx::empty(), d),
            Err(TypeError::InvalidRecursiveMetadata)
        );
    }
}

#[test]
fn negative_result_index_cannot_hide_in_annotations_beta_projections_or_cases() {
    let mut accepted = Vec::new();
    for wrapper in 0..5 {
        let mut s = Store::new();
        let empty = data(&mut s, vec![], vec![], vec![]);
        let nat = rock::nat_def(&mut s);
        let u = rock::type0(&mut s);
        let self_ = v(&mut s, 1);
        let de = app(&mut s, self_, &[empty]);
        let negative = s.terms.alloc(Term::Pi(de, empty));
        let wrapped = match wrapper {
            0 => s.terms.alloc(Term::Ann(negative, u)),
            1 => {
                let x = v(&mut s, 0);
                let id = lams(&mut s, 1, x);
                let ty = s.terms.alloc(Term::Pi(u, u));
                let id = s.terms.alloc(Term::Ann(id, ty));
                app(&mut s, id, &[negative])
            }
            2 | 3 => {
                let pair = s.terms.alloc(Term::Pair(negative, negative));
                let ty = s.terms.alloc(Term::Sigma(u, u));
                let pair = s.terms.alloc(Term::Ann(pair, ty));
                if wrapper == 2 {
                    s.terms.alloc(Term::Fst(pair))
                } else {
                    s.terms.alloc(Term::Snd(pair))
                }
            }
            _ => {
                let unit = data(&mut s, vec![], vec![], vec![ctor(vec![], vec![], vec![])]);
                let target = con(&mut s, unit, 0, vec![]);
                let motive = lams(&mut s, 1, u);
                s.terms.alloc(Term::Case {
                    target,
                    motive,
                    branches: vec![negative],
                })
            }
        };
        let d = data(
            &mut s,
            vec![],
            vec![u],
            vec![ctor(vec![], vec![], vec![wrapped])],
        );
        if infer(&mut s, Ctx::empty(), d).is_ok() {
            accepted.push(wrapper);
        }
        // Corresponding self-free wrapper behavior is covered by the core
        // normalization tests; this control keeps the result-index feature.
        let safe = s.terms.alloc(Term::Pi(nat, empty));
        let good = data(
            &mut s,
            vec![],
            vec![u],
            vec![ctor(vec![], vec![], vec![safe])],
        );
        infer(&mut s, Ctx::empty(), good).unwrap();
    }
    assert!(
        accepted.is_empty(),
        "accepted hidden negative result wrappers: {accepted:?}"
    );
}

#[test]
fn self_elimination_during_formation_is_rejected_without_reentry() {
    // Isolate a potential stack overflow in the regression subprocess.
    const CHILD: &str = "MENHERA_THIRD_PASS_FORMATION_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let out = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "self_elimination_during_formation_is_rejected_without_reentry",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "formation must reject, not recurse indefinitely: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        return;
    }
    let mut s = Store::new();
    let nat = rock::nat_def(&mut s);
    let zero = rock::nat_zero(&mut s, nat);
    // D : Nat -> Type0; base : D zero;
    // step : (r : D zero) -> D (case r of base => zero; step _ _ => zero).
    // The eliminator for D is not yet available while validating D itself.
    let self_ = v(&mut s, 1);
    let child_ty = app(&mut s, self_, &[zero]);
    let child = v(&mut s, 0);
    let motive = lams(&mut s, 1, nat);
    let step_branch = lams(&mut s, 2, zero);
    let index = s.terms.alloc(Term::Case {
        target: child,
        motive,
        branches: vec![zero, step_branch],
    });
    let d = data(
        &mut s,
        vec![],
        vec![nat],
        vec![
            ctor(vec![], vec![], vec![zero]),
            ctor(vec![child_ty], vec![true], vec![index]),
        ],
    );
    assert!(infer(&mut s, Ctx::empty(), d).is_err());
}

#[test]
fn result_index_can_eliminate_an_already_formed_field_type() {
    let mut s = Store::new();
    let nat = rock::nat_def(&mut s);
    let zero = rock::nat_zero(&mut s, nat);
    let one = rock::nat_suc(&mut s, nat, zero);
    let n = v(&mut s, 0);
    let motive = lams(&mut s, 1, nat);
    let ih = v(&mut s, 0);
    let succ = rock::nat_suc(&mut s, nat, ih);
    let step = lams(&mut s, 2, succ);
    let index = s.terms.alloc(Term::Case {
        target: n,
        motive,
        branches: vec![zero, step],
    });
    let d = data(
        &mut s,
        vec![],
        vec![nat],
        vec![ctor(vec![nat], vec![false], vec![index])],
    );
    infer(&mut s, Ctx::empty(), d).unwrap();
    let target = con(&mut s, d, 0, vec![one]);
    let ty = app(&mut s, d, &[one]);
    let target = s.terms.alloc(Term::Ann(target, ty));
    infer(&mut s, Ctx::empty(), target).unwrap();
    let branch = lams(&mut s, 1, n);
    let case = s.terms.alloc(Term::Case {
        target,
        motive,
        branches: vec![branch],
    });
    assert_nf(&mut s, case, one);
}

#[test]
fn result_self_position_includes_all_parameters_indices_and_fields() {
    let mut s = Store::new();
    let nat = rock::nat_def(&mut s);
    let zero = rock::nat_zero(&mut s, nat);
    let u = rock::type0(&mut s);
    let a = v(&mut s, 0);
    let b_ty = s.terms.alloc(Term::Pi(a, u));
    let empty = data(&mut s, vec![], vec![], vec![]);
    // Result context: self, index0, index1, A, B, x, y.
    let self_ = v(&mut s, 6);
    let a = v(&mut s, 3);
    let b = v(&mut s, 2);
    let recursive_type = app(&mut s, self_, &[a, b, nat, zero]);
    let negative = s.terms.alloc(Term::Pi(recursive_type, empty));
    let d = data(
        &mut s,
        vec![u, b_ty],
        vec![u, nat],
        vec![ctor(
            vec![nat, nat],
            vec![false, false],
            vec![negative, zero],
        )],
    );
    assert_eq!(
        infer(&mut s, Ctx::empty(), d),
        Err(TypeError::NotStrictlyPositive)
    );
    // At this result scope B is index 2; safe expressions mentioning
    // fields rather than self must not be rejected by an off-by-one check.
    let x = v(&mut s, 1);
    let good = data(
        &mut s,
        vec![u, b_ty],
        vec![u, nat],
        vec![ctor(vec![nat, nat], vec![false, false], vec![nat, x])],
    );
    infer(&mut s, Ctx::empty(), good).unwrap();
}
