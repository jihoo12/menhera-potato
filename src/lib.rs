//! rock — small trusted MLTT kernel with NBE and arena allocation.

pub mod arena;
pub mod check;
pub mod level;
pub mod nbe;
pub mod term;
pub mod value;

pub use arena::{Arena, Idx};
pub use check::{
    Ctx, TypeError, check, check_is_type, infer, nat_def, nat_lit, nat_suc, nat_type, nat_zero,
    type_n, type_var, type0,
};
pub use level::{Level, LevelBuilder, LevelId, eq_level, leq_level};
pub use nbe::{
    Store, apply, case_reduce, conv, eval, force_pi, force_sigma, force_univ, fst, normalize,
    quote, snd,
};
pub use term::{ConstructorDef, Term, TermBuilder, TermId};
pub use value::{Closure, Elim, Env, EnvId, Neutral, Spine, Value, ValueId};
