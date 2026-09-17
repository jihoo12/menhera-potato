# Formal System: menhera MLTT Kernel

This document describes the formal system implemented by the menhera (rock) kernel — a Martin-Löf Type Theory (MLTT) with predicative universes, dependent function types, dependent pair types, and general inductive types.

---

## 1. Syntax

### 1.1 Universe Levels

Levels are expressions built from:

```
ℓ ::= 0 | suc ℓ | max ℓ₁ ℓ₂ | α
```

where `α` is a rigid level variable (for universe polymorphism). Normalized levels have the canonical form `max(α₁+k₁, ..., αₙ+kₙ, k₀)` where each `kᵢ ≥ 0`.

### 1.2 Terms

| Constructor | Syntax | Description |
|---|---|---|
| Variable | `Var(i)` | de Bruijn index, 0 = innermost binder |
| Lambda | `Lam(b)` | λ-binding: `λ. b` |
| Pi | `Pi(A, B)` | Dependent function type: `Π A. B` (B binds one variable of type A) |
| Application | `App(f, a)` | `f a` |
| Universe | `Univ(ℓ)` | `Type ℓ` |
| Ascription | `Ann(m, A)` | Type annotation `m : A` (erased under evaluation) |
| Sigma | `Sigma(A, B)` | Dependent pair type: `Σ A. B` (B binds one variable of type A) |
| Pair | `Pair(a, b)` | `(a, b)` |
| Fst | `Fst(p)` | First projection `π₁ p` |
| Snd | `Snd(p)` | Second projection `π₂ p` |
| Inductive | `Inductive { level, params, indices, constructors }` | Inductive type definition |
| Constructor | `Con { def, idx, args, indices }` | Constructor application |
| Case | `Case { target, motive, branches }` | Case analysis / elimination |

#### Inductive Type Definition

An inductive type declaration `Inductive { level: ℓ, params: [A₁,...,Aₘ], indices: [I₁,...,Iₙ], constructors: [K₁,...,Kₖ] }` defines:

- A type `D` living at `Type ℓ`
- `m` parameters (shared across all constructors)
- `n` indices (varying per constructor)
- `k` constructors, each with a dependent telescope of argument types

Constructor body context layout (innermost first):

```
self : D | formal index slots | params | field₀ | field₁ | ...
```

The formal index slots exist only to keep the internal de Bruijn layout compatible with the family telescope. Constructor field types and result-index expressions must not refer to these slots directly; a varying index needed by a constructor must instead be represented by an explicit constructor field.

In argument type position `k`, `self` is at `Var(n + m + k)`.

#### Branch Telescope

For a constructor with `k` fields and `r` recursive occurrences, the corresponding case branch has `k + r` binders:

```
λ field₀. [ih₀ if recursive] field₁. [ih₁ if recursive] ... → result
```

Induction hypotheses are interleaved immediately after each recursive field.

### 1.3 Semantic Values (NbE Domain)

| Value | Description |
|---|---|
| `Lam(Closure)` | Lambda closure `(env, body)` |
| `Pi(V, Closure)` | Pi type: domain `V`, codomain closure |
| `Sigma(V, Closure)` | Sigma type: domain `V`, codomain closure |
| `Pair(V₁, V₂)` | Pair of values |
| `Univ(ℓ)` | Universe at level `ℓ` |
| `Inductive { def, args }` | Type family reference applied to accumulated args |
| `Con { def, idx, args, indices }` | Constructed value; `indices` is a legacy annotation payload and is empty for kernel-produced values |
| `Neut(Neutral)` | Stuck neutral term |

#### Neutral Terms

A neutral is a variable (de Bruijn *level*) with an elimination spine:

```
Neutral { level: ℓ, spine: Elim* }
```

Spine eliminations:
- `App(v)` — function application
- `Fst` — first projection
- `Snd` — second projection
- `Case { motive, branches }` — case analysis

#### Closure

A closure `(env, body)` is a term paired with a captured environment. Used for delayed substitution in binders.

---

## 2. Definitional Equality (≡)

Two terms are definitionally equal if they reduce to the same normal form. Implemented by semantic structural comparison with η-rules in `nbe::conv`.

### 2.1 Computation Rules

| Rule | Statement | Name |
|---|---|---|
| **β-red** | `(λ. b) a ≡ b[a/x]` | Beta reduction |
| **β-fst** | `fst (a, b) ≡ a` | Pair projection |
| **β-snd** | `snd (a, b) ≡ b` | Pair projection |
| **ι-red** | `case (K a₁…aᵣ) {…; bᵢ ⇒ eᵢ; …} ≡ eᵢ a₁…aᵣ ih₁…ihₛ` | Constructor reduction (iota) |
| **Ann-erase** | `(m : A) ≡ m` | Ascription erasure |

For iota reduction: the branch for constructor `Kᵢ` is applied to each constructor argument, and for each recursive argument, the induction hypothesis `case_reduce(motive, branches, arg)` is computed and applied.

### 2.2 Congruence Rules

| Rule | Statement |
|---|---|
| **Π-cong** | `A₁ ≡ A₂` and `B₁ ≡ B₂` (under fresh var) ⟹ `Π(x:A₁).B₁ ≡ Π(x:A₂).B₂` |
| **Σ-cong** | `A₁ ≡ A₂` and `B₁ ≡ B₂` (under fresh var) ⟹ `Σ(x:A₁).B₁ ≡ Σ(x:A₂).B₂` |
| **App-cong** | `f₁ ≡ f₂` and `a₁ ≡ a₂` ⟹ `f₁ a₁ ≡ f₂ a₂` |
| **Lam-cong** | `b₁ ≡ b₂` (under fresh var) ⟹ `λ. b₁ ≡ λ. b₂` |
| **Pair-cong** | `a₁ ≡ a₂` and `b₁ ≡ b₂` ⟹ `(a₁,b₁) ≡ (a₂,b₂)` |
| **Univ-cong** | `ℓ₁ = ℓ₂` ⟹ `Type ℓ₁ ≡ Type ℓ₂` |
| **Ind-cong** | same `def`, same `args` count, pairwise conversion ⟹ `Inductive ≡ Inductive` |
| **Con-cong** | same `def`, same `idx`, args pairwise conv, indices pairwise conv ⟹ `Con ≡ Con`; the indices comparison is vacuous for values produced by checked evaluation |
| **Neut-eq** | same `level`, same spine length, elim-by-elim conversion ⟹ `Neut ≡ Neut` |

### 2.3 η-Rules

| Rule | Statement |
|---|---|
| **η-fun** | `f ≡ λ. f` (Lam ≡ Neut: compare body with application of neutral to fresh var) |
| **η-pair** | `(fst p, snd p) ≡ p` (Pair ≡ Neut: compare projections) |

---

## 3. Bidirectional Type System

The kernel uses bidirectional typing: checking mode (⇐) and inference mode (⇒).

### 3.1 Context

A typing context `Γ` is a sequence of bound variables with their types:

```
Γ = x₁:A₁, x₂:A₂, ..., xₙ:Aₙ
```

Internally: `Ctx { types: EnvId, env: EnvId, depth: n }` where `types` maps each de Bruijn level to its type value, and `env` maps each level to a neutral variable.

### 3.2 Inference Rules (⇒)

Rules where the type is synthesized from the term:

#### Var
```
Γ(i) = A
─────────────────
Γ ⊢ Var(i) ⇒ A
```
Lookup the type of variable `i` in the context.

#### Univ
```
───────────────────────
Γ ⊢ Type ℓ ⇒ Type (suc ℓ)
```

#### Pi
```
Γ ⊢ A ⇒ Type ℓ₁    Γ, x:A ⊢ B ⇒ Type ℓ₂
─────────────────────────────────────────────
Γ ⊢ Π(x:A). B ⇒ Type (max ℓ₁ ℓ₂)
```

#### Sigma
```
Γ ⊢ A ⇒ Type ℓ₁    Γ, x:A ⊢ B ⇒ Type ℓ₂
─────────────────────────────────────────────
Γ ⊢ Σ(x:A). B ⇒ Type (max ℓ₁ ℓ₂)
```

#### App
```
Γ ⊢ f ⇒ Π(x:A). B    Γ ⊢ a ⇐ A
─────────────────────────────────────
Γ ⊢ f a ⇒ B[a/x]
```

#### Fst
```
Γ ⊢ p ⇒ Σ(x:A). B
─────────────────────
Γ ⊢ fst p ⇒ A
```

#### Snd
```
Γ ⊢ p ⇒ Σ(x:A). B
────────────────────────────────
Γ ⊢ snd p ⇒ B[(fst p)/x]
```

#### Ann
```
Γ ⊢ A ⇒ Type ℓ    Γ ⊢ m ⇐ A
───────────────────────────────
Γ ⊢ (m : A) ⇒ A
```

#### Con (inference mode, no parameters)
```
D is Inductive { params=[], indices, constructors }
Kᵢ is the i-th constructor with fields [F₁,...,Fₖ]
Γ ⊢ aⱼ ⇐ Fⱼ[prev_args/self/params/formal-index-slots]   for j = 1..k
(the formal index slots are layout placeholders and cannot occur in Fⱼ)
computed indices = eval(con_def.indices) with args bound
─────────────────────────────────────────────────────────────
Γ ⊢ Con { def: D, idx: i, args: [a₁,...,aₖ], ... } ⇒ D indices...
```

#### Con (checking mode, with expected type)
```
expected type = D p₁…pₘ i₁…iₙ (Inductive value with params and indices)
extract param_vals = [p₁,...,pₘ], expected_index_vals = [i₁,...,iₙ]
check each arg against field type in constructor env
verify computed indices ≡ expected indices
─────────────────────────────────────────────────────────────
Γ ⊢ Con { def: D, idx: i, args: [a₁,...,aₖ], ... } ⇐ D p₁…pₘ i₁…iₙ
```

#### Case
```
Γ ⊢ t ⇒ D p₁…pₘ i₁…iₙ
motive : (x : D p₁…i₁…) → Type ℓ  (uniform over fresh indices)
the runtime motive ABI is unary: indices are not additional motive arguments
branchᵢ has type: Π fields. [ih if recursive]... → P (K fields...)
  (for each constructor Kᵢ)
─────────────────────────────────────────────────────────────
Γ ⊢ case t { motive; branches } ⇒ motive(t)
```

#### Inductive (formation)
```
form_family checks:
1. Definition is closed (no captured outer locals)
2. Each param type and index type is a type (inhabits a universe)
3. Signature telescope: Π params. Π indices. Type ℓ
4. Strict positivity of all constructors
5. Each constructor field type is well-typed and within the declared universe
6. Result index expressions are well-typed
─────────────────────────────────────────────────────────────
Γ ⊢ Inductive { level: ℓ, params, indices, constructors } ⇒
    Π params. Π indices. Type ℓ
```

### 3.3 Checking Rules (⇐)

Rules where an expected type is provided:

#### Lam
```
force_pi(A) = (A₁, A₂)
Γ, x:A₁ ⊢ body ⇐ A₂[x]
─────────────────────────────
Γ ⊢ λ. body ⇐ Π(x:A₁). A₂
```

#### Pair
```
force_sigma(A) = (A₁, A₂)
Γ ⊢ a ⇐ A₁
Γ ⊢ b ⇐ A₂[a]
───────────────
Γ ⊢ (a, b) ⇐ Σ(x:A₁). A₂
```

#### Con (checking)
```
See Con checking mode in §3.2
```

#### Conversion
```
Γ ⊢ t ⇒ A    A ≡ B
─────────────────────
Γ ⊢ t ⇐ B
```

#### Cumulativity
```
Γ ⊢ t ⇒ Type ℓ₁    ℓ₁ ≤ ℓ₂
──────────────────────────────
Γ ⊢ t ⇐ Type ℓ₂
```

---

## 4. Normalization by Evaluation (NbE)

The kernel implements NbE with the following phases:

### 4.1 Evaluation (`eval`)

Maps syntax to semantic values under an environment:

| Term | Value |
|---|---|
| `Var(i)` | `env_lookup(env, i)` |
| `Lam(body)` | `Lam(env, body)` |
| `Pi(A, B)` | `Pi(eval(A), Closure(env, B))` |
| `Sigma(A, B)` | `Sigma(eval(A), Closure(env, B))` |
| `Pair(a, b)` | `Pair(eval(a), eval(b))` |
| `App(f, a)` | `apply(eval(f), eval(a))` |
| `Fst(p)` | `fst(eval(p))` |
| `Snd(p)` | `snd(eval(p))` |
| `Univ(ℓ)` | `Univ(ℓ)` |
| `Ann(m, _)` | `eval(m)` (ascription erased) |
| `Inductive{...}` | `Inductive { def: term, args: [] }` (args accumulated lazily via apply) |
| `Con{def, idx, args, indices}` | `Con { def, idx, eval(args), [] }`; `indices` is a checked annotation and is erased |
| `Case{target, motive, branches}` | `case_reduce(eval(motive), eval(branches), eval(target))` |

### 4.2 Application (`apply`)

| Function | Argument | Result |
|---|---|---|
| `Lam(env, body)` | `a` | `eval(body, env ∪ {a})` |
| `Inductive { def, args }` | `a` | `Inductive { def, args ++ [a] }` |
| `Neut(n)` | `a` | `Neut { n.level, spine ++ App(a) }` |

### 4.3 Projection (`fst`, `snd`)

| Pair | Result |
|---|---|
| `Pair(a, b)` | `a` (for fst) / `b` (for snd) |
| `Neut(n)` | `Neut { n.level, spine ++ Fst/Snd }` |

### 4.4 Case Reduction (`case_reduce`)

| Target | Result |
|---|---|
| `Con { def, idx, args, ... }` | Apply branch `idx` to each arg; for each recursive arg, compute `case_reduce(motive, branches, arg)` as IH and apply it |
| `Neut(n)` | `Neut { n.level, spine ++ Case { motive, branches } }` |

### 4.5 Quotation (`quote`)

Reads back a semantic value to a term at a given binder depth:

- Converts de Bruijn **level** (absolute) to de Bruijn **index** (relative): `index = depth - level - 1`
- For binders (Lam, Pi, Sigma): introduce a fresh variable, instantiate closure, quote body at `depth + 1`
- For Neut: quote the variable + replay spine eliminations as term constructors
- For Inductive with args: reconstruct as nested `App(def, quote(arg))...`
- For Con: quote each arg

### 4.6 Full Normalization

```
normalize(t) = quote(eval(t, empty_env), 0)
```

### 4.7 Closure Instantiation

```
inst(Closure(env, body), arg) = eval(body, env ∪ {arg})
```

---

## 5. Cumulativity

Universe levels support cumulativity via `leq_level`:

```
Type ℓ₁ : Type ℓ₂   when   ℓ₁ ≤ ℓ₂
```

Level comparison is a conservative decidable approximation, not the complete semantic ordering of symbolic `max` expressions:
- Constant offsets are compared directly
- Each level variable's individual offset must be ≤ the corresponding variable in the target

This allows `Type 0 : Type 1 : Type 2 : ...` and polymorphism with level variables.

---

## 6. Inductive Types

### 6.1 Formation

An inductive type `D` is declared with:
- Universe level `ℓ`
- Parameter telescope `p₁:A₁, ..., pₘ:Aₘ`
- Index telescope `i₁:I₁(p₁..), ..., iₙ:Iₙ(p₁..)`
- Constructor list `K₁, ..., Kₖ`

The type of `D` is:

```
D : Π(p₁:A₁). ... Π(pₘ:Aₘ). Π(i₁:I₁). ... Π(iₙ:Iₙ). Type ℓ
```

### 6.2 Constructor Typing

Constructor `Kⱼ` with fields `f₁:B₁, ..., fᵣ:Bᵣ` and result indices `e₁,...,eₙ`:

```
D self [formal index slots] params ⊢ B₁ : Type ℓⱼ
D self [formal index slots] params f₁:B₁ ⊢ B₂ : Type ℓⱼ
...
Γ_fields ⊢ eₖ : Iₖ(params, computed_indices)
─────────────────────────────────────────────
Kⱼ : Π params. Π f₁:B₁. ... Π fᵣ:Bᵣ. D params e₁...eₙ
```

Formal index slots are present in the internal constructor-body layout but are not binders in the constructor's introduction telescope. Field types and result-index expressions may depend on `self`, parameters, and preceding explicit fields as appropriate, but they must not refer directly to the formal index slots. Any varying index required by a constructor must be carried by an explicit field. Result index expressions are evaluated after all fields are bound and determine the indices of the constructed family value.

### 6.3 Strict Positivity

For each constructor argument at position `k`:

1. If the inductive type `D` does not occur in the argument type: **non-recursive** (`Recurrence::None`)
2. If `D` occurs, it must be a **saturated direct application**:
   - Head is `self` (the inductive type being defined)
   - Applied to exactly `params + indices` arguments
   - All arguments are self-free (do not reference `D`)
   - Parameter arguments must be the original parameters (identity substitution)
3. Recursive metadata flag must match the structural analysis exactly
4. Result index expressions must be self-free

This is a conservative subset: nested inductives, function types containing `D`, and `D` inside Sigma types are all rejected.

### 6.4 Elimination (Case Analysis)

```
case t as x in P { K₁ b₁ ⇒ e₁ ; ... ; Kₖ bₖ ⇒ eₖ } : P t
```

The motive `P` is a unary function from the inductive type to a universe. For indexed families, the checker validates it uniformly across fresh index variables, but the runtime ABI still passes only the target value; indices are not separate motive arguments. This is a restricted encoding rather than a general `Π indices. D params indices → Type` runtime recursor.

Branch type for constructor `Kⱼ` with fields `f₁,...,fᵣ` and recursive flags:

```
Π(f₁:B₁). [ih₁:P(f₁) if recursive] ... Π(fᵣ:Bᵣ). [ihᵣ:P(fᵣ) if recursive]. P(Kⱼ f₁...fᵣ)
```

### 6.5 Computational Behavior

- **iota-reduction**: `case (K a₁...aᵣ) branches = branch a₁...aᵣ ih₁...ihₛ`
  where `ihᵢ = case aᵢ branches` for each recursive argument `aᵢ`
- **Neutral case**: stuck case expressions accumulate on the spine

---

## 7. Variable Representation

The kernel uses two distinct variable representations:

| Representation | Scope | Use |
|---|---|---|
| de Bruijn **index** | Relative to binder (0 = innermost) | Syntax (`Term`) |
| de Bruijn **level** | Absolute binder depth in shared context | Semantic values (`Neutral`) |

Conversion between them during quote: `index = depth - level - 1`.

---

## 8. References

- Martin-Löf, P. (1984). *Intuitionistic Type Theory*. Bibliopolis. §1 pp. 13-15, §3 p. 24.
- Nordström, T., Petersson, K., & Smith, J.M. (1990). *Programming in Martin-Löf's Type Theory*. Oxford University Press. Chapter 8 "Datatypes".
- Coquand, T. & Paulin, C. (1988). "Inductively Defined Types". *COLOG-88*. §3 "Positivity condition".
- Giménez, E. (1996). "Codifying Guarded Definitions with Recursive Schemes". *TYPES'95*.
- Lean 4 kernel: `src/kernel/inductive.cpp`, `src/kernel/type_checker.cpp`.
- Agda 2.8.0: used as reference implementation for differential testing.
