//! Bidirectional typechecker for the MLTT kernel.

use crate::level::{self, Level, LevelBuilder, LevelId};
use crate::nbe::{self, Store};
use crate::term::{ConstructorDef, Term, TermId};
use crate::value::{EnvId, Value, ValueId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    ExpectedPi,
    ExpectedSigma,
    ExpectedUniv,
    ExpectedInductive,
    ConversionFailure,
    UnboundVariable {
        index: u32,
        depth: u32,
    },
    LevelMismatch,
    ConstructorArity {
        expected: usize,
        found: usize,
    },
    BranchArity {
        expected: usize,
        found: usize,
    },
    /// A constructor argument type places the inductive type being defined in a
    /// forbidden position (including positive shapes unsupported by the eliminator).
    ///
    /// Citation: Coquand & Paulin, "Inductively Defined Types", COLOG-88 (1988),
    /// §3 "Positivity condition"; Giménez, "Codifying Guarded Definitions with
    /// Recursive Schemes", TYPES'95 (1996).
    /// Reference implementations: Coq `kernel/inductive.ml` `check_positivity_one`;
    /// Agda `src/full/TypeChecking/Positivity.hs` `checkStrictlyPositive`.
    NotStrictlyPositive,
    /// Caller-supplied recursion flags disagree with constructor argument syntax.
    InvalidRecursiveMetadata,
    /// Con has no parameter arguments; use an expected type or annotation.
    CannotInferParameters,
    /// A constructor mentions a formal index not supplied as an explicit field.
    UnsupportedIndexDependency,
    /// Definitions have nominal identity and do not store a captured environment.
    /// Express dependencies on outer locals as explicit parameters instead.
    UnsupportedInductiveCapture,
}

pub type Result<T> = std::result::Result<T, TypeError>;

/// Typing context: environment of types (as values) + evaluation env of values.
#[derive(Debug, Clone, Copy, Default)]
pub struct Ctx {
    /// Types of bound variables (same spine shape as `env`).
    pub types: Option<EnvId>,
    /// Values of bound variables (neutrals for locals).
    pub env: Option<EnvId>,
    /// Binder depth (= number of locals).
    pub depth: u32,
}

impl Ctx {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn bind(self, store: &mut Store, ty: ValueId) -> Self {
        let var = nbe::fresh_var(store, self.depth);
        let types = Some(store.vb_extend_env(self.types, ty));
        let env = Some(store.vb_extend_env(self.env, var));
        Self {
            types,
            env,
            depth: self.depth + 1,
        }
    }
}

// Small helper on Store to avoid exposing ValueBuilder everywhere in check.
trait StoreExt {
    fn vb_extend_env(&mut self, parent: Option<EnvId>, value: ValueId) -> EnvId;
}

impl StoreExt for Store {
    fn vb_extend_env(&mut self, parent: Option<EnvId>, value: ValueId) -> EnvId {
        self.envs.alloc(crate::value::Env { parent, value })
    }
}

fn lookup_type(store: &Store, types: Option<EnvId>, index: u32) -> Result<ValueId> {
    let mut current = types;
    let mut i = index;
    loop {
        let Some(eid) = current else {
            return Err(TypeError::UnboundVariable {
                index,
                depth: store.envs.len() as u32,
            });
        };
        let frame = store.envs.get(eid);
        if i == 0 {
            return Ok(frame.value);
        }
        i -= 1;
        current = frame.parent;
    }
}

/// Instantiate a signature prefix in declaration order, never in body order.
/// Source: Lean 4 kernel/inductive.cpp, check_inductive_types/check_constructors.
fn extend_values(store: &mut Store, mut env: Option<EnvId>, values: &[ValueId]) -> Option<EnvId> {
    for &value in values {
        env = Some(store.vb_extend_env(env, value));
    }
    env
}

/// Explicit signature-to-body permutation. Only values move; syntax does not.
fn constructor_env(
    store: &mut Store,
    base: Option<EnvId>,
    self_val: ValueId,
    params: &[ValueId],
    indices: &[ValueId],
) -> Option<EnvId> {
    let env = Some(store.vb_extend_env(base, self_val));
    let env = extend_values(store, env, indices);
    extend_values(store, env, params)
}

/// Bind an already chosen semantic local (used when permuting the signature).
fn bind_value(store: &mut Store, ctx: Ctx, ty: ValueId, value: ValueId) -> Ctx {
    Ctx {
        env: Some(store.vb_extend_env(ctx.env, value)),
        types: Some(store.vb_extend_env(ctx.types, ty)),
        depth: ctx.depth + 1,
    }
}

/// Check the Pi telescope before evaluating its raw syntax. This prevents a
/// forward/free signature reference from reaching env_lookup.
/// Source: Lean 4 kernel/inductive.cpp, check_inductive_types.
fn form_family(
    store: &mut Store,
    ctx: Ctx,
    def: TermId,
    level: LevelId,
    params: &[TermId],
    indices: &[TermId],
    constructors: &[ConstructorDef],
) -> Result<ValueId> {
    // Nominal definitions are represented by TermId alone in values and quote.
    // Accepting a captured local would erase its substitution, identifying e.g.
    // Box Nat and Box Empty. Until definitions carry closures throughout NBE,
    // require closed declarations (explicit parameters remain supported).
    if (0..ctx.depth).any(|i| var_occurs(&store.terms, def, i)) {
        return Err(TypeError::UnsupportedInductiveCapture);
    }
    let mut signature_ctx = ctx;
    for &entry in params.iter().chain(indices) {
        let ty = check_is_type(store, signature_ctx, entry)?;
        signature_ctx = signature_ctx.bind(store, ty);
    }
    let mut signature = store.terms.alloc(Term::Univ(level));
    for &entry in params.iter().chain(indices).rev() {
        signature = store.terms.alloc(Term::Pi(entry, signature));
    }
    let family_ty = nbe::eval(store, ctx.env, signature);
    check_strict_positivity(&store.terms, constructors, indices.len(), params.len())?;

    // Allocate locals at their final BODY levels, then instantiate signature
    // types using these same values in SIGNATURE order. Index types may refer
    // to params even though the legacy body layout places indices first.
    let param_vals: Vec<_> = (0..params.len())
        .map(|j| nbe::fresh_var(store, ctx.depth + 1 + indices.len() as u32 + j as u32))
        .collect();
    let index_vals: Vec<_> = (0..indices.len())
        .map(|j| nbe::fresh_var(store, ctx.depth + 1 + j as u32))
        .collect();
    let mut sig_env = ctx.env;
    let mut param_types = Vec::new();
    let mut index_types = Vec::new();
    for (&tm, &val) in params.iter().zip(&param_vals) {
        param_types.push(nbe::eval(store, sig_env, tm));
        sig_env = Some(store.vb_extend_env(sig_env, val));
    }
    for (&tm, &val) in indices.iter().zip(&index_vals) {
        index_types.push(nbe::eval(store, sig_env, tm));
        sig_env = Some(store.vb_extend_env(sig_env, val));
    }
    let self_val = store.values.alloc(Value::Inductive { def, args: vec![] });
    let mut body_ctx = bind_value(store, ctx, family_ty, self_val);
    for (&ty, &val) in index_types.iter().zip(&index_vals) {
        body_ctx = bind_value(store, body_ctx, ty, val);
    }
    for (&ty, &val) in param_types.iter().zip(&param_vals) {
        body_ctx = bind_value(store, body_ctx, ty, val);
    }
    for con in constructors {
        if con.indices.len() != indices.len() {
            return Err(TypeError::ConstructorArity {
                expected: indices.len(),
                found: con.indices.len(),
            });
        }
        // Formal signature indices are not constructor fields. The evaluator
        // passes only fields to branches; any varying index must therefore be
        // bound explicitly as a field (as in Vec's n). Retain legacy slots for
        // compatibility, but reject references to these unbound implicit args.
        // Reference: Lean check_constructors/mk_rec_infos: constructor locals
        // consist of global parameters and explicit constructor fields.
        for (k, &tm) in con
            .arg_types
            .iter()
            .enumerate()
            .chain(con.indices.iter().map(|tm| (con.arg_types.len(), tm)))
        {
            for j in 0..indices.len() {
                if var_occurs(&store.terms, tm, (k + params.len() + j) as u32) {
                    return Err(TypeError::UnsupportedIndexDependency);
                }
            }
        }
        let mut field_ctx = body_ctx;
        for &tm in &con.arg_types {
            let sort = infer(store, field_ctx, tm)?;
            let field_level = nbe::force_univ(store, sort).ok_or(TypeError::ExpectedUniv)?;
            if !level::leq_level(&store.levels, field_level, level) {
                return Err(TypeError::LevelMismatch);
            }
            let ty = nbe::eval(store, field_ctx.env, tm);
            field_ctx = field_ctx.bind(store, ty);
        }
        // Result expressions live under ALL fields. Declared index types live
        // under params and PREVIOUS RESULT VALUES, not formal index variables.
        // Source: Lean check_constructors/is_valid_ind_app and type_checker::infer_app.
        let mut result_env = extend_values(store, ctx.env, &param_vals);
        for (&expression, &index_ty) in con.indices.iter().zip(indices) {
            let expected = nbe::eval(store, result_env, index_ty);
            check(store, field_ctx, expression, expected)?;
            let value = nbe::eval(store, field_ctx.env, expression);
            result_env = Some(store.vb_extend_env(result_env, value));
        }
    }
    Ok(family_ty)
}

/// Explicit index annotations use caller syntax, but declared index types use
/// the signature prefix. Check before eval, including non-inferable lambdas.
/// Source: Lean type_checker::infer_app, dependent application checking.
fn check_explicit_indices(
    store: &mut Store,
    ctx: Ctx,
    provided: &[TermId],
    index_types: &[TermId],
    computed: &[ValueId],
    params: &[ValueId],
) -> Result<()> {
    if provided.is_empty() {
        return Ok(());
    }
    if provided.len() != computed.len() {
        return Err(TypeError::ConstructorArity {
            expected: computed.len(),
            found: provided.len(),
        });
    }
    let mut sig_env = extend_values(store, ctx.env, params);
    for ((&tm, &ty), &expected) in provided.iter().zip(index_types).zip(computed) {
        let ty = nbe::eval(store, sig_env, ty);
        check(store, ctx, tm, ty)?;
        let value = nbe::eval(store, ctx.env, tm);
        if !nbe::conv(store, ctx.depth, value, expected) {
            return Err(TypeError::ConversionFailure);
        }
        sig_env = Some(store.vb_extend_env(sig_env, expected));
    }
    Ok(())
}

/// Unary motives are the existing evaluator ABI. Check their codomain really
/// is a universe (also for annotated or neutral motives).
fn check_motive(store: &mut Store, ctx: Ctx, tm: TermId, domain: ValueId) -> Result<ValueId> {
    if let Term::Lam(body) = *store.terms.get(tm) {
        let extended = ctx.bind(store, domain);
        let ty = infer(store, extended, body)?;
        nbe::force_univ(store, ty).ok_or(TypeError::ExpectedUniv)?;
    } else {
        let ty = infer(store, ctx, tm)?;
        let (dom, cod) = nbe::force_pi(store, ty).ok_or(TypeError::ExpectedPi)?;
        if !nbe::conv(store, ctx.depth, dom, domain) {
            return Err(TypeError::ConversionFailure);
        }
        let child = nbe::fresh_var(store, ctx.depth);
        let result = nbe::inst(store, cod, child);
        nbe::force_univ(store, result).ok_or(TypeError::ExpectedUniv)?;
    }
    Ok(nbe::eval(store, ctx.env, tm))
}

/// Build the branch telescope in the order used by `nbe::case_reduce`:
/// each constructor field, immediately followed by P(field) when recursive,
/// ending in P(K(fields)). Constructor syntax binds fields but never IHs.
///
/// Source: Lean 4 `src/kernel/inductive.cpp`, `add_inductive_fn::mk_rec_infos`
/// constructs IH types by applying the motive to each recursive field and the
/// result by applying it to the constructor. Lean groups IHs at the end; rock
/// interleaves these independent binders to match its existing computation rule.
/// https://github.com/leanprover/lean4/blob/master/src/kernel/inductive.cpp
fn build_branch_type(
    store: &mut Store,
    ctx: Ctx,
    target_args: &[ValueId],
    num_params: usize,
    con_def: &ConstructorDef,
    con_idx: usize,
    motive_val: ValueId,
    def: TermId,
) -> ValueId {
    let self_val = store.values.alloc(Value::Inductive { def, args: vec![] });
    let mut field_env = constructor_env(
        store,
        ctx.env,
        self_val,
        &target_args[..num_params],
        &target_args[num_params..],
    );

    let mut depth = ctx.depth;
    let mut domains = Vec::new();
    let mut fields = Vec::new();
    for (&arg_ty, &recursive) in con_def.arg_types.iter().zip(&con_def.recursive) {
        // Substitution uses the constructor's original field-only context.
        // Fresh variables carry levels in the actual interleaved telescope;
        // quote therefore accounts for every preceding field AND IH binder.
        let domain = nbe::eval(store, field_env, arg_ty);
        domains.push(nbe::quote(store, depth, domain));
        let field = nbe::fresh_var(store, depth);
        depth += 1;
        fields.push(field);
        field_env = Some(store.vb_extend_env(field_env, field));

        if recursive {
            let ih_ty = nbe::apply(store, motive_val, field);
            domains.push(nbe::quote(store, depth, ih_ty));
            depth += 1;
            // An IH occupies a branch binder but is not in constructor syntax.
            // It must not extend field_env or shift its de Bruijn lookup slots.
        }
    }

    let constructor = store.values.alloc(Value::Con {
        def,
        idx: con_idx,
        args: fields,
        indices: vec![],
    });
    let result = nbe::apply(store, motive_val, constructor);
    let mut telescope = nbe::quote(store, depth, result);
    // Domains were quoted at their own binder depths. Wrapping them requires
    // no shifting: each already refers to exactly the binders preceding it.
    for domain in domains.into_iter().rev() {
        telescope = store.terms.alloc(Term::Pi(domain, telescope));
    }
    nbe::eval(store, ctx.env, telescope)
}

/// Check that `term` has type `ty` (as a value).
pub fn check(store: &mut Store, ctx: Ctx, term: TermId, ty: ValueId) -> Result<()> {
    let term_clone = store.terms.get(term).clone();
    match term_clone {
        Term::Lam(body) => {
            let (domain, cod) = nbe::force_pi(store, ty).ok_or(TypeError::ExpectedPi)?;
            let ctx2 = ctx.bind(store, domain);
            // After bind, the bound value is the neutral at depth-1 of new ctx;
            // instantiate codomain with that value.
            let bound = crate::value::env_lookup(&store.envs, ctx2.env, 0);
            let cod_ty = nbe::inst(store, cod, bound);
            check(store, ctx2, body, cod_ty)
        }
        Term::Pair(fst, snd) => {
            let (domain, cod) = nbe::force_sigma(store, ty).ok_or(TypeError::ExpectedSigma)?;
            check(store, ctx, fst, domain)?;
            let fst_val = nbe::eval(store, ctx.env, fst);
            let snd_ty = nbe::inst(store, cod, fst_val);
            check(store, ctx, snd, snd_ty)
        }
        // Constructor checking: synthesize from the expected type when parameters
        // cannot be recovered from the constructor term alone.
        //
        // When the expected type is `D p₁…pₘ i₁…iₙ`, extract the param values
        // [p₁…pₘ] and expected index values [i₁…iₙ] from it, check the
        // constructor arguments, then verify the constructor's computed indices
        // (from con_def.indices) definitionally equal [i₁…iₙ].
        //
        // Citation: Nordström et al. (1990) Ch.8 p.83 — constructor typing rule.
        Term::Con {
            def,
            idx,
            ref args,
            indices: ref user_indices,
        } => {
            // Get the inductive definition
            let def_term = store.terms.get(def).clone();
            let (con_params, con_indices_def, constructors) = match def_term {
                Term::Inductive {
                    params,
                    indices,
                    constructors: cs,
                    ..
                } => (params, indices, cs),
                _ => return Err(TypeError::ExpectedInductive),
            };

            // Verify the expected type is this inductive applied to the right # of args
            let expected_applied_args = match store.values.get(ty).clone() {
                Value::Inductive {
                    def: ety_def,
                    args: ety_args,
                } => {
                    if ety_def != def {
                        // Expected type is a different inductive — fall through to infer path
                        return check_con_via_infer(store, ctx, term, ty);
                    }
                    ety_args
                }
                _ => {
                    // Expected type is not an inductive — fall through to infer path
                    return check_con_via_infer(store, ctx, term, ty);
                }
            };

            let num_params = con_params.len();
            let num_idx_types = con_indices_def.len();
            let expected_total = num_params + num_idx_types;
            if expected_applied_args.len() != expected_total {
                return Err(TypeError::ConversionFailure);
            }

            // Extract param values and expected index values from the applied args
            let param_vals: Vec<ValueId> = expected_applied_args[..num_params].to_vec();
            let expected_index_vals: Vec<ValueId> = expected_applied_args[num_params..].to_vec();

            check_strict_positivity(
                &store.terms,
                &constructors,
                con_indices_def.len(),
                con_params.len(),
            )?;

            // Definitions may arrive directly through Con, without formation.
            infer(store, ctx, def)?;

            if idx >= constructors.len() {
                return Err(TypeError::ExpectedInductive);
            }
            let con_def = &constructors[idx];

            if args.len() != con_def.arg_types.len() {
                return Err(TypeError::ConstructorArity {
                    expected: con_def.arg_types.len(),
                    found: args.len(),
                });
            }

            let raw_ind_val = store.values.alloc(Value::Inductive { def, args: vec![] });
            let mut eval_env = constructor_env(
                store,
                ctx.env,
                raw_ind_val,
                &param_vals,
                &expected_index_vals,
            );

            // Check each constructor argument against its type (evaluated in eval_env)
            // Argument terms all live in the unchanged caller context. Only
            // eval_env grows: stored field types bind self/family entries and
            // exactly the preceding constructor fields, never branch IHs.
            // This is telescope instantiation, as in Lean 4
            // src/kernel/type_checker.cpp, type_checker::infer_app: check the
            // argument in the caller context, then substitute it into the type.
            // https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp
            for (arg_tm, &arg_ty_tm) in args.iter().zip(&con_def.arg_types) {
                let arg_ty_val = nbe::eval(store, eval_env, arg_ty_tm);
                check(store, ctx, *arg_tm, arg_ty_val)?;
                let arg_val = nbe::eval(store, ctx.env, *arg_tm);
                eval_env = Some(store.vb_extend_env(eval_env, arg_val));
            }

            // Evaluate the constructor's fixed index expressions in the arg-extended eval env
            let con_index_vals: Vec<ValueId> = con_def
                .indices
                .iter()
                .map(|&idx_expr| nbe::eval(store, eval_env, idx_expr))
                .collect();

            // Verify the constructor's computed indices match the expected indices
            if con_index_vals.len() != expected_index_vals.len() {
                return Err(TypeError::ConversionFailure);
            }
            for (&computed, &expected) in con_index_vals.iter().zip(expected_index_vals.iter()) {
                if !nbe::conv(store, ctx.depth, computed, expected) {
                    return Err(TypeError::ConversionFailure);
                }
            }

            check_explicit_indices(
                store,
                ctx,
                user_indices,
                &con_indices_def,
                &con_index_vals,
                &param_vals,
            )?;

            Ok(())
        }
        _ => {
            let inferred = infer(store, ctx, term)?;
            if nbe::conv(store, ctx.depth, inferred, ty) {
                Ok(())
            } else {
                // Cumulativity for universes: inferred ≤ expected
                match (nbe::force_univ(store, inferred), nbe::force_univ(store, ty)) {
                    (Some(li), Some(le)) if level::leq_level(&store.levels, li, le) => Ok(()),
                    _ => Err(TypeError::ConversionFailure),
                }
            }
        }
    }
}

/// Fallback: check a `Term::Con` by inferring its type and comparing via `conv`.
/// Used when the expected type is not a matching `Value::Inductive`.
fn check_con_via_infer(store: &mut Store, ctx: Ctx, term: TermId, ty: ValueId) -> Result<()> {
    let inferred = infer(store, ctx, term)?;
    if nbe::conv(store, ctx.depth, inferred, ty) {
        Ok(())
    } else {
        Err(TypeError::ConversionFailure)
    }
}

/// Infer the type of `term`.
pub fn infer(store: &mut Store, ctx: Ctx, term: TermId) -> Result<ValueId> {
    let term_clone = store.terms.get(term).clone();
    match term_clone {
        Term::Var(i) => {
            if i >= ctx.depth {
                return Err(TypeError::UnboundVariable {
                    index: i,
                    depth: ctx.depth,
                });
            }
            lookup_type(store, ctx.types, i)
        }
        Term::Univ(level) => {
            let suc = {
                let mut b = LevelBuilder {
                    levels: &mut store.levels,
                };
                b.suc(level)
            };
            Ok(store.values.alloc(Value::Univ(suc)))
        }
        Term::Inductive {
            level,
            params,
            indices,
            constructors,
        } => form_family(store, ctx, term, level, &params, &indices, &constructors),
        Term::Con {
            def,
            idx,
            ref args,
            ref indices,
        } => {
            // Constructor introduction: K(a1,...,ak) : D params... indices...
            // where K is the idx-th constructor of D
            // Citation: Martin-Löf (1984) §1 p.15;
            // Nordström et al. (1990) Ch.8 p.83
            let def_term = store.terms.get(def).clone();
            let (con_params, con_indices_def, constructors) = match def_term {
                Term::Inductive {
                    params,
                    indices,
                    constructors: cs,
                    ..
                } => (params, indices, cs),
                _ => return Err(TypeError::ExpectedInductive),
            };

            check_strict_positivity(
                &store.terms,
                &constructors,
                con_indices_def.len(),
                con_params.len(),
            )?;

            // Definitions may arrive directly through Con, without formation.
            infer(store, ctx, def)?;

            if idx >= constructors.len() {
                return Err(TypeError::ExpectedInductive);
            }
            let con_def = &constructors[idx];

            if args.len() != con_def.arg_types.len() {
                return Err(TypeError::ConstructorArity {
                    expected: con_def.arg_types.len(),
                    found: args.len(),
                });
            }

            // Note: user-supplied Con.indices are optional — the typechecker
            // derives canonical index values from con_def.indices. We verify
            // them (if provided) later after evaluating constructor args.

            if !con_params.is_empty() {
                return Err(TypeError::CannotInferParameters);
            }
            let ind_val = nbe::eval(store, ctx.env, def);
            // Formal slots cannot occur in validated constructor syntax.
            let index_slots: Vec<_> = (0..con_indices_def.len())
                .map(|i| nbe::fresh_var(store, ctx.depth + i as u32))
                .collect();
            let mut eval_env = constructor_env(store, ctx.env, ind_val, &[], &index_slots);

            // Argument terms all live in the unchanged caller context. Only
            // eval_env grows: stored field types bind self/family entries and
            // exactly the preceding constructor fields, never branch IHs.
            // This is telescope instantiation, as in Lean 4
            // src/kernel/type_checker.cpp, type_checker::infer_app: check the
            // argument in the caller context, then substitute it into the type.
            // https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp
            for (arg_tm, &arg_ty_tm) in args.iter().zip(&con_def.arg_types) {
                let arg_ty_val = nbe::eval(store, eval_env, arg_ty_tm);
                check(store, ctx, *arg_tm, arg_ty_val)?;
                let arg_val = nbe::eval(store, ctx.env, *arg_tm);
                eval_env = Some(store.vb_extend_env(eval_env, arg_val));
            }

            // For indexed inductive types, evaluate the constructor's fixed index
            // expressions in the argument-extended eval env.  These are the
            // canonical index values that this constructor always produces.
            //
            // Citation: Nordström et al. (1990) Ch.8 p.83 — each constructor
            // specifies which index value it introduces; the typechecker must
            // check that the expected type's index agrees with this value.
            let con_index_vals: Vec<ValueId> = con_def
                .indices
                .iter()
                .map(|&idx_expr| nbe::eval(store, eval_env, idx_expr))
                .collect();

            check_explicit_indices(store, ctx, indices, &con_indices_def, &con_index_vals, &[])?;

            // Return the inductive type applied to params and the constructor's
            // canonical index values (not the user-supplied ones, which may be
            // absent or were already verified above).
            let mut result = ind_val;
            // Apply to the constructor's computed index values
            for idx_val in con_index_vals {
                result = nbe::apply(store, result, idx_val);
            }
            Ok(result)
        }
        Term::Case {
            target,
            motive,
            ref branches,
        } => {
            // Case elimination: case t as x in P { K1 => b1 ; ... ; Kn => bn } : P t
            // Unary indexed motives are checked uniformly over fresh indices.
            // Citation: Martin-Löf (1984) §1 p.15, §3 p.24;
            // Nordström et al. (1990) Ch.8 p.84
            let target_ty = infer(store, ctx, target)?;

            // target_ty is now always Value::Inductive { def, args } where args contains
            // all applied params and indices (thanks to the new NBE representation).
            // For non-indexed/non-parameterized types, args is empty.
            let (target_def, target_args) = match store.values.get(target_ty).clone() {
                Value::Inductive { def, args } => (def, args),
                _ => return Err(TypeError::ExpectedInductive),
            };

            let (ind_params, ind_indices, constructors) = {
                let def_term = store.terms.get(target_def).clone();
                match def_term {
                    Term::Inductive {
                        params,
                        indices,
                        constructors: cs,
                        ..
                    } => (params, indices, cs),
                    _ => return Err(TypeError::ExpectedInductive),
                }
            };

            check_strict_positivity(
                &store.terms,
                &constructors,
                ind_indices.len(),
                ind_params.len(),
            )?;

            infer(store, ctx, target_def)?;
            if target_args.len() != ind_params.len() + ind_indices.len() {
                return Err(TypeError::ExpectedInductive);
            }
            let motive_val = check_motive(store, ctx, motive, target_ty)?;
            if !ind_indices.is_empty() {
                // Indexed elimination fixes parameters but quantifies over ALL
                // indices. The unary motive syntax must work uniformly at each
                // fiber. Requote its checked value to weaken caller references
                // into the generic-index context; never reinterpret raw syntax.
                // Source: Lean mk_rec_infos, motive Pi over indices and major.
                // This is its index-independent syntax fragment, preserving
                // rock's unary runtime motive ABI without adding NbE rules.
                let mut generic_ctx = ctx;
                let params = &target_args[..ind_params.len()];
                let mut sig_env = extend_values(store, ctx.env, params);
                let mut generic_args = params.to_vec();
                for &index_ty in &ind_indices {
                    let ty = nbe::eval(store, sig_env, index_ty);
                    let index = nbe::fresh_var(store, generic_ctx.depth);
                    generic_ctx = generic_ctx.bind(store, ty);
                    sig_env = Some(store.vb_extend_env(sig_env, index));
                    generic_args.push(index);
                }
                let generic_ty = store.values.alloc(Value::Inductive {
                    def: target_def,
                    args: generic_args,
                });
                let generic_motive = nbe::quote(store, generic_ctx.depth, motive_val);
                check_motive(store, generic_ctx, generic_motive, generic_ty)?;
            }

            // Check each branch
            if branches.len() != constructors.len() {
                return Err(TypeError::BranchArity {
                    expected: constructors.len(),
                    found: branches.len(),
                });
            }

            for (branch_tm, (con_idx, con_def)) in
                branches.iter().zip(constructors.iter().enumerate())
            {
                let branch_ty = build_branch_type(
                    store,
                    ctx,
                    &target_args,
                    ind_params.len(),
                    con_def,
                    con_idx,
                    motive_val,
                    target_def,
                );
                check(store, ctx, *branch_tm, branch_ty)?;
            }

            // Return motive applied to target value.
            // For non-indexed types: P(target)
            // The runtime motive receives only the target; no extra index
            // applications are inserted in the result or in IH types.
            let target_val = nbe::eval(store, ctx.env, target);
            let result = nbe::apply(store, motive_val, target_val);
            Ok(result)
        }
        Term::Pi(domain, codomain) => {
            let dom_ty = infer(store, ctx, domain)?;
            let l1 = nbe::force_univ(store, dom_ty).ok_or(TypeError::ExpectedUniv)?;
            let domain_val = nbe::eval(store, ctx.env, domain);
            let ctx2 = ctx.bind(store, domain_val);
            let cod_ty = infer(store, ctx2, codomain)?;
            let l2 = nbe::force_univ(store, cod_ty).ok_or(TypeError::ExpectedUniv)?;
            let max = {
                let mut b = LevelBuilder {
                    levels: &mut store.levels,
                };
                b.max(l1, l2)
            };
            Ok(store.values.alloc(Value::Univ(max)))
        }
        Term::Sigma(domain, codomain) => {
            let dom_ty = infer(store, ctx, domain)?;
            let l1 = nbe::force_univ(store, dom_ty).ok_or(TypeError::ExpectedUniv)?;
            let domain_val = nbe::eval(store, ctx.env, domain);
            let ctx2 = ctx.bind(store, domain_val);
            let cod_ty = infer(store, ctx2, codomain)?;
            let l2 = nbe::force_univ(store, cod_ty).ok_or(TypeError::ExpectedUniv)?;
            let max = {
                let mut b = LevelBuilder {
                    levels: &mut store.levels,
                };
                b.max(l1, l2)
            };
            Ok(store.values.alloc(Value::Univ(max)))
        }
        Term::Lam(_) => {
            // Bare λ is not inferable in this bidirectional discipline.
            Err(TypeError::ExpectedPi)
        }
        Term::Pair(_, _) => {
            // Bare pair is not inferable without type annotation.
            Err(TypeError::ExpectedSigma)
        }
        Term::App(fun, arg) => {
            let fun_ty = infer(store, ctx, fun)?;
            let (domain, cod) = nbe::force_pi(store, fun_ty).ok_or(TypeError::ExpectedPi)?;
            check(store, ctx, arg, domain)?;
            let arg_val = nbe::eval(store, ctx.env, arg);
            Ok(nbe::inst(store, cod, arg_val))
        }
        Term::Fst(p) => {
            let p_ty = infer(store, ctx, p)?;
            let (domain, _) = nbe::force_sigma(store, p_ty).ok_or(TypeError::ExpectedSigma)?;
            Ok(domain)
        }
        Term::Snd(p) => {
            let p_ty = infer(store, ctx, p)?;
            let (_, cod) = nbe::force_sigma(store, p_ty).ok_or(TypeError::ExpectedSigma)?;
            let p_val = nbe::eval(store, ctx.env, p);
            let fst_val = nbe::fst(store, p_val);
            Ok(nbe::inst(store, cod, fst_val))
        }
        Term::Ann(tm, ty) => {
            let ty_val = check_is_type(store, ctx, ty)?;
            check(store, ctx, tm, ty_val)?;
            Ok(ty_val)
        }
    }
}

// ─── Structural recurrence analysis ─────────────────────────────────────────

/// Whether an argument can be passed directly to `nbe::case_reduce` for its IH.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Recurrence {
    None,
    Direct,
}

/// Free occurrence of the de Bruijn *index* `d`, including nested definitions.
/// Binder accounting follows `infer`'s Inductive formation context, not a fresh
/// closed scope: self, indices, parameters, then successive constructor args.
fn var_occurs(terms: &crate::arena::Arena<Term>, tm: TermId, d: u32) -> bool {
    match terms.get(tm) {
        Term::Var(i) => *i == d,
        Term::Lam(b) => var_occurs(terms, *b, d + 1),
        Term::Pi(a, b) | Term::Sigma(a, b) => {
            var_occurs(terms, *a, d) || var_occurs(terms, *b, d + 1)
        }
        Term::App(a, b) | Term::Ann(a, b) | Term::Pair(a, b) => {
            var_occurs(terms, *a, d) || var_occurs(terms, *b, d)
        }
        Term::Fst(p) | Term::Snd(p) => var_occurs(terms, *p, d),
        Term::Univ(_) => false,
        Term::Inductive {
            params,
            indices,
            constructors,
            ..
        } => {
            // The family signature is also evaluated as a Pi telescope in the
            // outer context: parameters first, then indices (without self).
            // Constructor bodies have a separate self/indices/params layout;
            // signature syntax is never visited under that layout.
            for (j, &ty) in params.iter().chain(indices).enumerate() {
                if var_occurs(terms, ty, d + j as u32) {
                    return true;
                }
            }
            let inner_d = d + 1 + params.len() as u32 + indices.len() as u32;
            constructors.iter().any(|con| {
                con.arg_types
                    .iter()
                    .enumerate()
                    .any(|(k, &ty)| var_occurs(terms, ty, inner_d + k as u32))
                    || con
                        .indices
                        .iter()
                        .any(|&idx| var_occurs(terms, idx, inner_d + con.arg_types.len() as u32))
            })
        }
        Term::Con {
            def, args, indices, ..
        } => {
            var_occurs(terms, *def, d)
                || args.iter().chain(indices).any(|&a| var_occurs(terms, a, d))
        }
        Term::Case {
            target,
            motive,
            branches,
        } => {
            var_occurs(terms, *target, d)
                || var_occurs(terms, *motive, d)
                || branches.iter().any(|&b| var_occurs(terms, b, d))
        }
    }
}

/// Conservative subset of strict positivity: only D-free types and saturated
/// direct D applications. Source: Lean 4 `src/kernel/inductive.cpp`,
/// `check_positivity`, `is_valid_ind_app`, and `is_rec_argument`:
/// https://github.com/leanprover/lean4/blob/master/src/kernel/inductive.cpp
/// Unlike Lean's general recursor construction, rock's `nbe::case_reduce`
/// recurses on the argument itself. Thus even positive Pi/Sigma/nested shapes
/// are rejected here. No normalization is used to hide syntactic occurrences.
fn recurrence(
    terms: &crate::arena::Arena<Term>,
    tm: TermId,
    d: u32,
    num_indices: usize,
    num_params: usize,
    k: usize,
) -> Result<Recurrence> {
    if !var_occurs(terms, tm, d) {
        return Ok(Recurrence::None);
    }
    let mut head = tm;
    let mut args = Vec::new();
    while let Term::App(f, x) = terms.get(head) {
        args.push(*x);
        head = *f;
    }
    args.reverse();
    if !matches!(terms.get(head), Term::Var(i) if *i == d)
        || args.len() != num_params + num_indices
        || args.iter().any(|&arg| var_occurs(terms, arg, d))
    {
        return Err(TypeError::NotStrictlyPositive);
    }
    // Recursive calls retain the family's parameters. Indices may vary;
    // ordinary argument typechecking checks their types and saturation.
    for (j, &arg) in args.iter().take(num_params).enumerate() {
        let param = (k + num_params - 1 - j) as u32;
        if !matches!(terms.get(arg), Term::Var(i) if *i == param) {
            return Err(TypeError::NotStrictlyPositive);
        }
    }
    Ok(Recurrence::Direct)
}

/// Validate flags from the same structural analysis that enforces positivity.
/// D is at `num_indices + num_params + k` in the k-th argument type.
/// This is a representation invariant for the direct recursive-argument rule
/// above, not an additional typing or computation rule.
fn check_strict_positivity(
    terms: &crate::arena::Arena<Term>,
    constructors: &[ConstructorDef],
    num_indices: usize,
    num_params: usize,
) -> Result<()> {
    for con in constructors {
        if con.recursive.len() != con.arg_types.len() {
            return Err(TypeError::InvalidRecursiveMetadata);
        }
        for (k, (&arg_ty, &flag)) in con.arg_types.iter().zip(&con.recursive).enumerate() {
            let d = (num_indices + num_params + k) as u32;
            let actual = recurrence(terms, arg_ty, d, num_indices, num_params, k)?;
            if flag != (actual == Recurrence::Direct) {
                return Err(TypeError::InvalidRecursiveMetadata);
            }
        }
    }
    Ok(())
}

/// Check that `term` is a type (inhabits some universe) and return its value.
pub fn check_is_type(store: &mut Store, ctx: Ctx, term: TermId) -> Result<ValueId> {
    let ty = infer(store, ctx, term)?;
    let _ = nbe::force_univ(store, ty).ok_or(TypeError::ExpectedUniv)?;
    Ok(nbe::eval(store, ctx.env, term))
}

/// Infer and return both the type value and evaluated term value.
pub fn infer_val(store: &mut Store, ctx: Ctx, term: TermId) -> Result<(ValueId, ValueId)> {
    let ty = infer(store, ctx, term)?;
    let val = nbe::eval(store, ctx.env, term);
    Ok((ty, val))
}

/// Convenience: allocate `Type 0`.
pub fn type0(store: &mut Store) -> TermId {
    let l0 = store.levels.alloc(Level::Zero);
    store.terms.alloc(Term::Univ(l0))
}

/// Convenience: allocate `Type (suc^n 0)`.
pub fn type_n(store: &mut Store, n: u32) -> TermId {
    let mut b = LevelBuilder {
        levels: &mut store.levels,
    };
    let level = b.const_level(n);
    store.terms.alloc(Term::Univ(level))
}

/// Convenience: allocate `Type α` for level variable `α`.
pub fn type_var(store: &mut Store, var: u32) -> (TermId, LevelId) {
    let level = store.levels.alloc(Level::Var(var));
    let tm = store.terms.alloc(Term::Univ(level));
    (tm, level)
}

/// Convenience: build the Nat inductive type definition.
/// data Nat : Type 0 where zero : Nat ; suc : Nat → Nat
pub fn nat_def(store: &mut Store) -> TermId {
    let zero_con = ConstructorDef {
        name: "zero".to_string(),
        arg_types: vec![],
        recursive: vec![],
        indices: vec![],
    };
    let suc_con = ConstructorDef {
        name: "suc".to_string(),
        arg_types: vec![store.terms.alloc(Term::Var(0))], // Var(0) = self (Nat)
        recursive: vec![true],
        indices: vec![],
    };
    let l0 = store.levels.alloc(Level::Zero);
    store.terms.alloc(Term::Inductive {
        level: l0,
        params: vec![],
        indices: vec![],
        constructors: vec![zero_con, suc_con],
    })
}

/// Convenience: allocate `Nat` type term.
pub fn nat_type(store: &mut Store) -> TermId {
    nat_def(store)
}

/// Convenience: build `zero : Nat`.
pub fn nat_zero(store: &mut Store, def: TermId) -> TermId {
    store.terms.alloc(Term::Con {
        def,
        idx: 0,
        args: vec![],
        indices: vec![],
    })
}

/// Convenience: build `suc n : Nat`.
pub fn nat_suc(store: &mut Store, def: TermId, n: TermId) -> TermId {
    store.terms.alloc(Term::Con {
        def,
        idx: 1,
        args: vec![n],
        indices: vec![],
    })
}

/// Convenience: allocate numeral `n` as nested `Con` applications.
pub fn nat_lit(store: &mut Store, n: u32) -> TermId {
    let def = nat_def(store);
    let mut tm = nat_zero(store, def);
    for _ in 0..n {
        tm = nat_suc(store, def, tm);
    }
    tm
}
