//! Core MLTT syntax (Π / λ / App / Univ / Σ / Pair / Projections), arena-allocated.

use crate::arena::{Arena, Idx};
use crate::level::LevelId;

pub type TermId = Idx<Term>;

/// De Bruijn indices in binders; 0 is the innermost binder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Local variable (de Bruijn index).
    Var(u32),
    /// \λ. body\
    Lam(TermId),
    /// \Π A. B\ — \B\ binds one variable of type \A\.
    Pi(TermId, TermId),
    /// \ a\
    App(TermId, TermId),
    /// Universe \Type ℓ\
    Univ(LevelId),
    /// Type ascription `m : ty` (enables inferring annotated lambdas).
    Ann(TermId, TermId),
    /// \Σ A. B\ — \B\ binds one variable of type \A\.
    Sigma(TermId, TermId),
    /// Pair \(a, b)\
    Pair(TermId, TermId),
    /// First projection \st p\
    Fst(TermId),
    /// Second projection `snd p`
    Snd(TermId),
    /// User-defined inductive type definition.
    ///
    /// Constructor body context is extended by self, then indices, then params.
    /// In argument type k (with k earlier arguments bound), self is Var(i+p+k),
    /// parameters occupy Var(k..k+p), and earlier arguments Var(0..k).
    /// Each group is innermost first. Constructor result indices are checked
    /// after all constructor arguments have been bound. Formal index slots
    /// are retained for layout compatibility but may not occur in field/result
    /// syntax: varying indices must be supplied as explicit constructor fields.
    ///
    /// Citation: Martin-Löf (1984) §1 "General frameworks", p. 13-15;
    /// Nordström, Petersson, Smith (1990) Chapter 8, "Datatypes"
    Inductive {
        level: LevelId,
        /// Signature telescope: entry j sees the caller and j earlier params.
        /// It sees neither self nor indices. For Vec A: [Type 0].
        params: Vec<TermId>,
        /// Signature telescope: entry j sees all params and j earlier indices.
        /// Index 0 is the nearest preceding binder; self is not in scope.
        indices: Vec<TermId>,
        constructors: Vec<ConstructorDef>,
    },
    /// Application of a constructor to an inductive type.
    ///
    /// Citation: Martin-Löf (1984) §1 p.15; Nordström et al. (1990) Ch.8 p.83
    Con {
        /// Reference to the Inductive term that defines this type
        def: TermId,
        /// Index into the inductive type's constructor list
        idx: usize,
        /// Arguments to the constructor
        args: Vec<TermId>,
        /// Index expressions for this constructor application.
        /// For non-indexed types: empty.
        /// For indexed types: the computed index values (e.g., [zero] for nil, [suc n] for cons).
        indices: Vec<TermId>,
    },
    /// Case analysis / elimination for an inductive type.
    ///
    /// Each branch is a lambda-like term. For a constructor with k arguments
    /// and r recursive occurrences, the branch has k + r parameters:
    /// - Each constructor argument in order
    /// - Immediately after a recursive argument, its IH: ih_i : P(arg_i)
    ///
    /// Citation: Martin-Löf (1984) §1 p.15, §3 p.24;
    /// Nordström et al. (1990) Ch.8 p.84 ("case analysis")
    Case {
        target: TermId,
        /// Unary motive from the scrutinee to a universe. For indexed families
        /// it must typecheck uniformly across fresh indices with params fixed.
        /// Indices are implicit in this syntax, not additional runtime arguments.
        motive: TermId,
        /// One branch per constructor (lambdas, see above)
        branches: Vec<TermId>,
    },
}

/// Definition of a single constructor within an inductive type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorDef {
    pub name: String,
    /// Sequential argument types; earlier arguments introduce binders.
    /// Self is Var(indices.len() + params.len() + k) in argument type k.
    pub arg_types: Vec<TermId>,
    /// One flag per argument, validated by the kernel against its syntax.
    /// True means a direct, saturated self application with unchanged parameters
    /// and self-free indices, suitable for direct recursion in case reduction.
    pub recursive: Vec<bool>,
    /// Index expressions for this constructor.
    /// These are terms that compute the index values when this constructor is applied.
    /// Use the body context extended by all constructor arguments.
    /// For non-indexed types (Nat, Bool): empty.
    /// For Vec: the length index expression (e.g., suc n for nil/suc).
    pub indices: Vec<TermId>,
}

/// Term construction helpers.
pub struct TermBuilder<'a> {
    pub terms: &'a mut Arena<Term>,
}

impl<'a> TermBuilder<'a> {
    pub fn var(&mut self, idx: u32) -> TermId {
        self.terms.alloc(Term::Var(idx))
    }

    pub fn lam(&mut self, body: TermId) -> TermId {
        self.terms.alloc(Term::Lam(body))
    }

    pub fn pi(&mut self, domain: TermId, codomain: TermId) -> TermId {
        self.terms.alloc(Term::Pi(domain, codomain))
    }

    pub fn app(&mut self, fun: TermId, arg: TermId) -> TermId {
        self.terms.alloc(Term::App(fun, arg))
    }

    pub fn univ(&mut self, level: LevelId) -> TermId {
        self.terms.alloc(Term::Univ(level))
    }

    pub fn ann(&mut self, tm: TermId, ty: TermId) -> TermId {
        self.terms.alloc(Term::Ann(tm, ty))
    }

    pub fn sigma(&mut self, domain: TermId, codomain: TermId) -> TermId {
        self.terms.alloc(Term::Sigma(domain, codomain))
    }

    pub fn pair(&mut self, fst: TermId, snd: TermId) -> TermId {
        self.terms.alloc(Term::Pair(fst, snd))
    }

    pub fn fst(&mut self, pair: TermId) -> TermId {
        self.terms.alloc(Term::Fst(pair))
    }

    pub fn snd(&mut self, pair: TermId) -> TermId {
        self.terms.alloc(Term::Snd(pair))
    }

    pub fn inductive(
        &mut self,
        level: LevelId,
        params: Vec<TermId>,
        indices: Vec<TermId>,
        constructors: Vec<ConstructorDef>,
    ) -> TermId {
        self.terms.alloc(Term::Inductive {
            level,
            params,
            indices,
            constructors,
        })
    }

    pub fn con(
        &mut self,
        def: TermId,
        idx: usize,
        args: Vec<TermId>,
        indices: Vec<TermId>,
    ) -> TermId {
        self.terms.alloc(Term::Con {
            def,
            idx,
            args,
            indices,
        })
    }

    pub fn case(&mut self, target: TermId, motive: TermId, branches: Vec<TermId>) -> TermId {
        self.terms.alloc(Term::Case {
            target,
            motive,
            branches,
        })
    }
}
