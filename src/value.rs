//! Semantic values and neutrals for NBE.

use crate::arena::{Arena, Idx};
use crate::level::LevelId;
use crate::term::TermId;

pub type ValueId = Idx<Value>;
pub type EnvId = Idx<Env>;
pub type SpineId = Idx<Spine>;

/// Environment: list of values for bound variables (de Bruijn: index 0 = last).
#[derive(Debug, Clone)]
pub struct Env {
    /// Parent environment (outer binders), or none for empty.
    pub parent: Option<EnvId>,
    /// Value bound at this frame.
    pub value: ValueId,
}

/// Elimination forms for neutrals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Elim {
    /// Function application: `f arg`
    App(ValueId),
    /// First projection: `fst p`
    Fst,
    /// Second projection: `snd p`
    Snd,
    /// Case analysis on neutral inductive value.
    /// Citation: Martin-Löf (1984) §1 p.15; Nordström et al. (1990) Ch.8 p.84
    Case {
        motive: ValueId,
        branches: Vec<ValueId>,
    },
}

/// Elimination spine for neutrals (applied left-to-right).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spine {
    pub parent: Option<SpineId>,
    pub elim: Elim,
}

/// Closure: delayed substitution `(env, body)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Closure {
    pub env: Option<EnvId>,
    pub body: TermId,
}

/// Neutral head: stuck variable (de Bruijn *level*).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Neutral {
    /// Absolute binder depth (level) of the free variable.
    pub level: u32,
    pub spine: Option<SpineId>,
}

/// Semantic values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    /// `λ` closure
    Lam(Closure),
    /// `Π` with evaluated domain and closure codomain
    Pi(ValueId, Closure),
    /// `Σ` with evaluated domain and closure codomain
    Sigma(ValueId, Closure),
    /// Pair `(a, b)`
    Pair(ValueId, ValueId),
    /// `Type ℓ`
    Univ(LevelId),
    /// User-defined inductive type (reference to term-level definition),
    /// optionally applied to parameters and/or index arguments.
    /// `args` holds the values of all applied arguments in order
    /// (params first, then indices), accumulated as the type family is
    /// applied.  For a fully-saturated `Vec A n`, args = [A, n].
    Inductive { def: TermId, args: Vec<ValueId> },
    /// Constructor application: constructed value of an inductive type
    Con {
        def: TermId,
        idx: usize,
        args: Vec<ValueId>,
        /// Index values for indexed types
        indices: Vec<ValueId>,
    },
    /// Neutral stuck term
    Neut(Neutral),
}

pub struct ValueBuilder<'a> {
    pub values: &'a mut Arena<Value>,
    pub envs: &'a mut Arena<Env>,
    pub spines: &'a mut Arena<Spine>,
}

impl<'a> ValueBuilder<'a> {
    pub fn lam(&mut self, env: Option<EnvId>, body: TermId) -> ValueId {
        self.values.alloc(Value::Lam(Closure { env, body }))
    }

    pub fn pi(&mut self, domain: ValueId, env: Option<EnvId>, body: TermId) -> ValueId {
        self.values.alloc(Value::Pi(domain, Closure { env, body }))
    }

    pub fn sigma(&mut self, domain: ValueId, env: Option<EnvId>, body: TermId) -> ValueId {
        self.values
            .alloc(Value::Sigma(domain, Closure { env, body }))
    }

    pub fn pair(&mut self, fst: ValueId, snd: ValueId) -> ValueId {
        self.values.alloc(Value::Pair(fst, snd))
    }

    pub fn univ(&mut self, level: LevelId) -> ValueId {
        self.values.alloc(Value::Univ(level))
    }

    pub fn inductive(&mut self, def: TermId, args: Vec<ValueId>) -> ValueId {
        self.values.alloc(Value::Inductive { def, args })
    }

    pub fn con(
        &mut self,
        def: TermId,
        idx: usize,
        args: Vec<ValueId>,
        indices: Vec<ValueId>,
    ) -> ValueId {
        self.values.alloc(Value::Con {
            def,
            idx,
            args,
            indices,
        })
    }

    pub fn neut_var(&mut self, level: u32) -> ValueId {
        self.values
            .alloc(Value::Neut(Neutral { level, spine: None }))
    }

    pub fn extend_env(&mut self, parent: Option<EnvId>, value: ValueId) -> EnvId {
        self.envs.alloc(Env { parent, value })
    }

    pub fn extend_spine(&mut self, parent: Option<SpineId>, elim: Elim) -> SpineId {
        self.spines.alloc(Spine { parent, elim })
    }

    pub fn apply_neut(&mut self, neut: Neutral, arg: ValueId) -> ValueId {
        let spine = Some(self.extend_spine(neut.spine, Elim::App(arg)));
        self.values.alloc(Value::Neut(Neutral {
            level: neut.level,
            spine,
        }))
    }

    pub fn fst_neut(&mut self, neut: Neutral) -> ValueId {
        let spine = Some(self.extend_spine(neut.spine, Elim::Fst));
        self.values.alloc(Value::Neut(Neutral {
            level: neut.level,
            spine,
        }))
    }

    pub fn snd_neut(&mut self, neut: Neutral) -> ValueId {
        let spine = Some(self.extend_spine(neut.spine, Elim::Snd));
        self.values.alloc(Value::Neut(Neutral {
            level: neut.level,
            spine,
        }))
    }

    pub fn case_neut(&mut self, neut: Neutral, motive: ValueId, branches: Vec<ValueId>) -> ValueId {
        let spine = Some(self.extend_spine(neut.spine, Elim::Case { motive, branches }));
        self.values.alloc(Value::Neut(Neutral {
            level: neut.level,
            spine,
        }))
    }
}

/// Lookup de Bruijn index in an environment chain.
pub fn env_lookup(envs: &Arena<Env>, env: Option<EnvId>, index: u32) -> ValueId {
    let mut current = env;
    let mut i = index;
    loop {
        let Some(eid) = current else {
            panic!("environment underflow looking up index {index}");
        };
        let frame = envs.get(eid);
        if i == 0 {
            return frame.value;
        }
        i -= 1;
        current = frame.parent;
    }
}

/// Collect spine eliminations in application order (outermost first).
pub fn spine_elims(spines: &Arena<Spine>, spine: Option<SpineId>) -> Vec<Elim> {
    let mut elims = Vec::new();
    let mut current = spine;
    while let Some(sid) = current {
        let frame = spines.get(sid);
        elims.push(frame.elim.clone());
        current = frame.parent;
    }
    elims.reverse();
    elims
}

/// Collect spine args in application order (outermost first).
/// Ignores non-application eliminations.
pub fn spine_args(spines: &Arena<Spine>, spine: Option<SpineId>) -> Vec<ValueId> {
    spine_elims(spines, spine)
        .into_iter()
        .filter_map(|e| match e {
            Elim::App(arg) => Some(arg),
            _ => None,
        })
        .collect()
}

/// Depth of an environment (number of binders).
pub fn env_depth(envs: &Arena<Env>, env: Option<EnvId>) -> u32 {
    let mut depth = 0;
    let mut current = env;
    while let Some(eid) = current {
        depth += 1;
        current = envs.get(eid).parent;
    }
    depth
}
