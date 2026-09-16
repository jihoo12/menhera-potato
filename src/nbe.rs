//! Normalization by evaluation: eval, apply, quote, conversion.

use crate::arena::Arena;
use crate::level::{self, Level, LevelId};
use crate::term::{Term, TermId};
use crate::value::{
    Closure, Elim, Env, EnvId, Neutral, Spine, Value, ValueBuilder, ValueId, env_depth, env_lookup,
    spine_elims,
};

/// Shared kernel store for NBE.
pub struct Store {
    pub terms: Arena<Term>,
    pub values: Arena<Value>,
    pub envs: Arena<Env>,
    pub spines: Arena<Spine>,
    pub levels: Arena<Level>,
}

impl Store {
    pub fn new() -> Self {
        Self {
            terms: Arena::new(),
            values: Arena::new(),
            envs: Arena::new(),
            spines: Arena::new(),
            levels: Arena::new(),
        }
    }

    pub fn clear(&mut self) {
        self.terms.clear();
        self.values.clear();
        self.envs.clear();
        self.spines.clear();
        self.levels.clear();
    }

    fn vb(&mut self) -> ValueBuilder<'_> {
        ValueBuilder {
            values: &mut self.values,
            envs: &mut self.envs,
            spines: &mut self.spines,
        }
    }
}

impl Default for Store {
    fn default() -> Self {
        Self::new()
    }
}

pub fn eval(store: &mut Store, env: Option<EnvId>, term: TermId) -> ValueId {
    let term_clone = store.terms.get(term).clone();
    match term_clone {
        Term::Var(i) => env_lookup(&store.envs, env, i),
        Term::Lam(body) => store.vb().lam(env, body),
        Term::Pi(domain, codomain) => {
            let d = eval(store, env, domain);
            store.vb().pi(d, env, codomain)
        }
        Term::Sigma(domain, codomain) => {
            let d = eval(store, env, domain);
            store.vb().sigma(d, env, codomain)
        }
        Term::Pair(fst_tm, snd_tm) => {
            let a = eval(store, env, fst_tm);
            let b = eval(store, env, snd_tm);
            store.vb().pair(a, b)
        }
        Term::Fst(p) => {
            let pv = eval(store, env, p);
            fst(store, pv)
        }
        Term::Snd(p) => {
            let pv = eval(store, env, p);
            snd(store, pv)
        }
        Term::App(fun, arg) => {
            let f = eval(store, env, fun);
            let a = eval(store, env, arg);
            apply(store, f, a)
        }
        Term::Univ(level) => store.vb().univ(level),
        Term::Inductive {
            ref params,
            ref indices,
            ..
        } => {
            // Return a bare Inductive value.  Arguments are accumulated lazily
            // when `apply` is called on it (see apply branch for Inductive).
            // This ensures `BoolIdx true` and `BoolIdx false` remain distinct
            // values rather than collapsing to the same `Inductive { def }`.
            //
            // Citation: Martin-Löf (1984) §1 p.13-15;
            // Nordström et al. (1990) Ch.8 p.82 — type families are functions.
            let _ = (params, indices); // params/indices recorded in the term, not the value
            store.vb().inductive(term, vec![])
        }
        Term::Con {
            def,
            idx,
            args,
            indices,
        } => {
            let args_val: Vec<ValueId> = args.into_iter().map(|a| eval(store, env, a)).collect();
            let indices_val: Vec<ValueId> =
                indices.into_iter().map(|i| eval(store, env, i)).collect();
            store.vb().con(def, idx, args_val, indices_val)
        }
        Term::Case {
            target,
            motive,
            branches,
        } => {
            let tgt = eval(store, env, target);
            let m = eval(store, env, motive);
            let bs: Vec<ValueId> = branches.into_iter().map(|b| eval(store, env, b)).collect();
            case_reduce(store, m, bs, tgt)
        }
        // Ascriptions erase under evaluation.
        Term::Ann(tm, _) => eval(store, env, tm),
    }
}

pub fn apply(store: &mut Store, fun: ValueId, arg: ValueId) -> ValueId {
    match store.values.get(fun).clone() {
        Value::Lam(Closure { env, body }) => {
            let new_env = store.vb().extend_env(env, arg);
            eval(store, Some(new_env), body)
        }
        // Applying a type family (parameterized/indexed inductive) accumulates the arg.
        // e.g. Vec applied to Bool gives Vec Bool, which is still Inductive { Vec, [Bool] }.
        Value::Inductive { def, mut args } => {
            args.push(arg);
            store.vb().inductive(def, args)
        }
        Value::Neut(n) => store.vb().apply_neut(n, arg),
        _ => {
            panic!("cannot apply non-function value");
        }
    }
}

pub fn fst(store: &mut Store, pair: ValueId) -> ValueId {
    match *store.values.get(pair) {
        Value::Pair(a, _) => a,
        Value::Neut(n) => store.vb().fst_neut(n),
        _ => panic!("cannot take fst of non-pair value"),
    }
}

pub fn snd(store: &mut Store, pair: ValueId) -> ValueId {
    match *store.values.get(pair) {
        Value::Pair(_, b) => b,
        Value::Neut(n) => store.vb().snd_neut(n),
        _ => panic!("cannot take snd of non-pair value"),
    }
}

/// Case analysis evaluation for inductive types.
///
/// Rules:
/// - ι-reduction: case Con(def, idx, args) { branches } ≡ branches[idx] args... ih_args...
///   where ih_args are the induction hypotheses for recursive arguments
/// - Neutral: stuck neutral target pushes Case onto the spine
///
/// Citation: Martin-Löf (1984) §1 p.15; Nordström et al. (1990) Ch.8 p.84
pub fn case_reduce(
    store: &mut Store,
    motive: ValueId,
    branches: Vec<ValueId>,
    target: ValueId,
) -> ValueId {
    let target_val = store.values.get(target).clone();
    match target_val {
        Value::Con {
            def,
            idx,
            args,
            indices: _,
        } => {
            // Get the constructor definition from the term arena
            let def_term = store.terms.get(def).clone();
            let constructors = match def_term {
                Term::Inductive {
                    constructors: cs, ..
                } => cs,
                _ => panic!("case target def is not an Inductive"),
            };
            let con_def = &constructors[idx];

            // Select the branch for this constructor
            let branch = branches[idx];

            // Apply branch to constructor args interleaved with induction hypotheses.
            // For each arg: apply arg, then if recursive apply ih = case_reduce(motive, branches, arg).
            let mut result = branch;
            for (arg, &is_recursive) in args.iter().zip(&con_def.recursive) {
                result = apply(store, result, *arg);
                if is_recursive {
                    let ih = case_reduce(store, motive, branches.clone(), *arg);
                    result = apply(store, result, ih);
                }
            }
            result
        }
        Value::Neut(n) => store.vb().case_neut(n, motive, branches),
        _ => panic!("cannot apply case to non-inductive value"),
    }
}

/// Instantiate a closure with an argument.
pub fn inst(store: &mut Store, clos: Closure, arg: ValueId) -> ValueId {
    let env = store.vb().extend_env(clos.env, arg);
    eval(store, Some(env), clos.body)
}

/// Quote a value at the given binder depth into a term.
pub fn quote(store: &mut Store, depth: u32, value: ValueId) -> TermId {
    let value_clone = store.values.get(value).clone();
    match value_clone {
        Value::Lam(clos) => {
            let var = store.vb().neut_var(depth);
            let body_val = inst(store, clos, var);
            let body = quote(store, depth + 1, body_val);
            store.terms.alloc(Term::Lam(body))
        }
        Value::Pi(domain, clos) => {
            let d = quote(store, depth, domain);
            let var = store.vb().neut_var(depth);
            let cod_val = inst(store, clos, var);
            let c = quote(store, depth + 1, cod_val);
            store.terms.alloc(Term::Pi(d, c))
        }
        Value::Sigma(domain, clos) => {
            let d = quote(store, depth, domain);
            let var = store.vb().neut_var(depth);
            let cod_val = inst(store, clos, var);
            let c = quote(store, depth + 1, cod_val);
            store.terms.alloc(Term::Sigma(d, c))
        }
        Value::Pair(fst_val, snd_val) => {
            let a = quote(store, depth, fst_val);
            let b = quote(store, depth, snd_val);
            store.terms.alloc(Term::Pair(a, b))
        }
        Value::Univ(level) => store.terms.alloc(Term::Univ(level)),
        Value::Inductive { def, args } => {
            // Quote back the Inductive type former applied to any accumulated args.
            let mut tm = def;
            for arg in args {
                let a = quote(store, depth, arg);
                tm = store.terms.alloc(Term::App(tm, a));
            }
            tm
        }
        Value::Con {
            def,
            idx,
            args,
            indices,
        } => {
            let args_tm: Vec<TermId> = args.into_iter().map(|a| quote(store, depth, a)).collect();
            let indices_tm: Vec<TermId> = indices
                .into_iter()
                .map(|i| quote(store, depth, i))
                .collect();
            store.terms.alloc(Term::Con {
                def,
                idx,
                args: args_tm,
                indices: indices_tm,
            })
        }
        Value::Neut(Neutral { level, spine }) => {
            // Convert de Bruijn level → index relative to `depth`.
            let idx = depth
                .checked_sub(level + 1)
                .expect("neutral level out of range while quoting");
            let mut tm = store.terms.alloc(Term::Var(idx));
            for elim in spine_elims(&store.spines, spine) {
                match elim {
                    Elim::App(arg) => {
                        let a = quote(store, depth, arg);
                        tm = store.terms.alloc(Term::App(tm, a));
                    }
                    Elim::Fst => {
                        tm = store.terms.alloc(Term::Fst(tm));
                    }
                    Elim::Snd => {
                        tm = store.terms.alloc(Term::Snd(tm));
                    }
                    Elim::Case { motive, branches } => {
                        let m = quote(store, depth, motive);
                        let bs: Vec<TermId> = branches
                            .into_iter()
                            .map(|b| quote(store, depth, b))
                            .collect();
                        tm = store.terms.alloc(Term::Case {
                            target: tm,
                            motive: m,
                            branches: bs,
                        });
                    }
                }
            }
            tm
        }
    }
}

/// Definitional equality of values via quoting and structural compare,
/// with level comparison for universes and η for functions/Π and pairs/Σ.
pub fn conv(store: &mut Store, depth: u32, a: ValueId, b: ValueId) -> bool {
    let a_val = store.values.get(a).clone();
    let b_val = store.values.get(b).clone();
    match (a_val, b_val) {
        (Value::Univ(la), Value::Univ(lb)) => level::eq_level(&store.levels, la, lb),
        (Value::Pi(da, ca), Value::Pi(db, cb)) | (Value::Sigma(da, ca), Value::Sigma(db, cb)) => {
            if !conv(store, depth, da, db) {
                return false;
            }
            let var = store.vb().neut_var(depth);
            let va = inst(store, ca, var);
            let vb = inst(store, cb, var);
            conv(store, depth + 1, va, vb)
        }
        (Value::Lam(ca), Value::Lam(cb)) => {
            let var = store.vb().neut_var(depth);
            let va = inst(store, ca, var);
            let vb = inst(store, cb, var);
            conv(store, depth + 1, va, vb)
        }
        // η: lam ~ neut  ⟺  body ~ neut var
        (Value::Lam(ca), Value::Neut(_)) => {
            let var = store.vb().neut_var(depth);
            let va = inst(store, ca, var);
            let app = apply(store, b, var);
            conv(store, depth + 1, va, app)
        }
        (Value::Neut(_), Value::Lam(cb)) => {
            let var = store.vb().neut_var(depth);
            let vb = inst(store, cb, var);
            let app = apply(store, a, var);
            conv(store, depth + 1, app, vb)
        }
        // Pair structural conversion:
        (Value::Pair(a1, b1), Value::Pair(a2, b2)) => {
            conv(store, depth, a1, a2) && conv(store, depth, b1, b2)
        }
        // η: pair ~ neut  ⟺  fst ~ fst(neut) ∧ snd ~ snd(neut)
        (Value::Pair(a1, b1), Value::Neut(_)) => {
            let fst_b = fst(store, b);
            let snd_b = snd(store, b);
            conv(store, depth, a1, fst_b) && conv(store, depth, b1, snd_b)
        }
        (Value::Neut(_), Value::Pair(a2, b2)) => {
            let fst_a = fst(store, a);
            let snd_a = snd(store, a);
            conv(store, depth, fst_a, a2) && conv(store, depth, snd_a, b2)
        }
        // Inductive type equality: same definition and same applied args
        // (handles both bare inductives and applied type families like Vec A n).
        (Value::Inductive { def: da, args: ref aa }, Value::Inductive { def: db, args: ref ab }) => {
            if da != db || aa.len() != ab.len() {
                return false;
            }
            aa.iter()
                .zip(ab.iter())
                .all(|(&a, &b)| conv(store, depth, a, b))
        }
        // Constructor equality: same def, same idx, args conv, indices conv
        (
            Value::Con {
                def: da,
                idx: ia,
                args: ref aa,
                indices: ref ia_idx,
            },
            Value::Con {
                def: db,
                idx: ib,
                args: ref ab,
                indices: ref ib_idx,
            },
        ) => {
            if da != db || ia != ib || aa.len() != ab.len() || ia_idx.len() != ib_idx.len() {
                return false;
            }
            aa.iter()
                .zip(ab.iter())
                .all(|(&a, &b)| conv(store, depth, a, b))
                && ia_idx
                    .iter()
                    .zip(ib_idx.iter())
                    .all(|(&a, &b)| conv(store, depth, a, b))
        }
        (Value::Neut(na), Value::Neut(nb)) => {
            if na.level != nb.level {
                return false;
            }
            let elims_a = spine_elims(&store.spines, na.spine);
            let elims_b = spine_elims(&store.spines, nb.spine);
            if elims_a.len() != elims_b.len() {
                return false;
            }
            for (ea, eb) in elims_a.into_iter().zip(elims_b) {
                match (ea, eb) {
                    (Elim::App(xa), Elim::App(xb)) => {
                        if !conv(store, depth, xa, xb) {
                            return false;
                        }
                    }
                    (Elim::Fst, Elim::Fst) => {}
                    (Elim::Snd, Elim::Snd) => {}
                    (
                        Elim::Case {
                            motive: ma,
                            branches: ref ba,
                        },
                        Elim::Case {
                            motive: mb,
                            branches: ref bb,
                        },
                    ) => {
                        if !conv(store, depth, ma, mb) || ba.len() != bb.len() {
                            return false;
                        }
                        for (x, y) in ba.iter().zip(bb.iter()) {
                            if !conv(store, depth, *x, *y) {
                                return false;
                            }
                        }
                    }
                    _ => return false,
                }
            }
            true
        }
        _ => false,
    }
}

/// Evaluate under empty env and quote back (full normalization).
pub fn normalize(store: &mut Store, term: TermId) -> TermId {
    let val = eval(store, None, term);
    quote(store, 0, val)
}

/// Force a value expected to be a Π; returns (domain, closure).
pub fn force_pi(store: &Store, ty: ValueId) -> Option<(ValueId, Closure)> {
    match *store.values.get(ty) {
        Value::Pi(d, c) => Some((d, c)),
        _ => None,
    }
}

/// Force a value expected to be a Σ; returns (domain, closure).
pub fn force_sigma(store: &Store, ty: ValueId) -> Option<(ValueId, Closure)> {
    match *store.values.get(ty) {
        Value::Sigma(d, c) => Some((d, c)),
        _ => None,
    }
}

/// Force a value expected to be a universe; returns its level.
pub fn force_univ(store: &Store, ty: ValueId) -> Option<LevelId> {
    match *store.values.get(ty) {
        Value::Univ(l) => Some(l),
        _ => None,
    }
}

/// Fresh rigid variable at the current context depth (for checking).
pub fn fresh_var(store: &mut Store, depth: u32) -> ValueId {
    store.vb().neut_var(depth)
}

pub fn env_len(store: &Store, env: Option<EnvId>) -> u32 {
    env_depth(&store.envs, env)
}
