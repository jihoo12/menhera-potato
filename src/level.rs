//! Universe levels for polymorphic universes.

use crate::arena::{Arena, Idx};

pub type LevelId = Idx<Level>;

/// Universe level expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level {
    Zero,
    Suc(LevelId),
    Max(LevelId, LevelId),
    /// Rigid level variable (for universe polymorphism).
    Var(u32),
}

/// Normalize a level into a comparable shape: `max(vars..., suc^k(0))` style.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormLevel {
    /// Constant offset from zero (number of successors on the base).
    pub offset: u32,
    /// Level variables, each with an extra successor offset.
    pub vars: Vec<(u32, u32)>,
}

impl NormLevel {
    pub fn zero() -> Self {
        Self {
            offset: 0,
            vars: Vec::new(),
        }
    }

    pub fn suc(mut self) -> Self {
        self.offset += 1;
        for v in &mut self.vars {
            v.1 += 1;
        }
        self
    }

    pub fn max(mut self, other: NormLevel) -> Self {
        self.offset = self.offset.max(other.offset);
        for (var, off) in other.vars {
            if let Some(existing) = self.vars.iter_mut().find(|(v, _)| *v == var) {
                existing.1 = existing.1.max(off);
            } else {
                self.vars.push((var, off));
            }
        }
        self.vars.sort_by_key(|(v, _)| *v);
        self
    }
}

pub fn normalize(levels: &Arena<Level>, id: LevelId) -> NormLevel {
    match *levels.get(id) {
        Level::Zero => NormLevel::zero(),
        Level::Suc(inner) => normalize(levels, inner).suc(),
        Level::Max(a, b) => normalize(levels, a).max(normalize(levels, b)),
        Level::Var(v) => NormLevel {
            offset: 0,
            vars: vec![(v, 0)],
        },
    }
}

/// Definitional level equality after normalization.
pub fn eq_level(levels: &Arena<Level>, a: LevelId, b: LevelId) -> bool {
    normalize(levels, a) == normalize(levels, b)
}

/// Cumulativity: `a ≤ b` on normalized levels.
///
/// Conservative: concrete offsets compare numerically; variables must match
/// with offset ≤, and extra vars on the smaller side are rejected.
pub fn leq_level(levels: &Arena<Level>, a: LevelId, b: LevelId) -> bool {
    let na = normalize(levels, a);
    let nb = normalize(levels, b);

    if na.offset > nb.offset {
        return false;
    }

    for (var, off_a) in &na.vars {
        match nb.vars.iter().find(|(v, _)| v == var) {
            Some((_, off_b)) if off_a <= off_b => {}
            _ => return false,
        }
    }

    // If `a` is pure constant and `b` has vars, still ok when offset ≤
    // (e.g. 0 ≤ max(α, 0)). Extra vars on `b` only raise the level.
    true
}

/// Helpers to build levels in an arena.
pub struct LevelBuilder<'a> {
    pub levels: &'a mut Arena<Level>,
}

impl<'a> LevelBuilder<'a> {
    pub fn zero(&mut self) -> LevelId {
        self.levels.alloc(Level::Zero)
    }

    pub fn suc(&mut self, inner: LevelId) -> LevelId {
        self.levels.alloc(Level::Suc(inner))
    }

    pub fn max(&mut self, a: LevelId, b: LevelId) -> LevelId {
        self.levels.alloc(Level::Max(a, b))
    }

    pub fn var(&mut self, v: u32) -> LevelId {
        self.levels.alloc(Level::Var(v))
    }

    pub fn const_level(&mut self, n: u32) -> LevelId {
        let mut id = self.zero();
        for _ in 0..n {
            id = self.suc(id);
        }
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suc_leq() {
        let mut levels = Arena::new();
        let l0 = {
            let mut b = LevelBuilder {
                levels: &mut levels,
            };
            b.zero()
        };
        let l1 = {
            let mut b = LevelBuilder {
                levels: &mut levels,
            };
            b.suc(l0)
        };
        let l2 = {
            let mut b = LevelBuilder {
                levels: &mut levels,
            };
            b.suc(l1)
        };
        let l1b = {
            let mut b = LevelBuilder {
                levels: &mut levels,
            };
            b.const_level(1)
        };
        assert!(leq_level(&levels, l0, l1));
        assert!(leq_level(&levels, l1, l2));
        assert!(!leq_level(&levels, l2, l1));
        assert!(eq_level(&levels, l1, l1b));
    }

    #[test]
    fn max_normalize() {
        let mut levels = Arena::new();
        let mut b = LevelBuilder {
            levels: &mut levels,
        };
        let a = b.var(0);
        let z = b.zero();
        let m = b.max(a, z);
        let n = normalize(&levels, m);
        assert_eq!(n.offset, 0);
        assert_eq!(n.vars, vec![(0, 0)]);
    }
}
