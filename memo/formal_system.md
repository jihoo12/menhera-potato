# Formal System: menhera MLTT Kernel

This document describes the formal system implemented by the menhera (rock) kernel — a Martin-Löf Type Theory (MLTT) with predicative universes, dependent function types, dependent pair types, and a restricted fragment of parameterized/indexed inductive types. This is an implementation description, not a proof of kernel soundness.

---

## 1. Syntax

### 1.1 Universe Levels

Levels are expressions built from:

```
ℓ ::= 0 | suc ℓ | max ℓ₁ ℓ₂ | α
```

where `α` is a rigid level variable (for universe polymorphism). Normalized levels have the implementation-normalized form `max(α₁+k₁, ..., αₙ+kₙ, k₀)` where each `kᵢ ≥ 0`.

Normalization retains a separate constant offset, merges repeated variables by their maximum offset, and sorts variables. Equality compares these records. For example, `suc α` and `max(suc α, 1)` have equal records. Level equality here means `eq_level`, not equality of raw level IDs.

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

- A family `D` whose fully applied instances live at `Type ℓ`
- `m` parameters (shared across all constructors)
- `n` indices (varying per constructor)
- `k` constructors, each with a dependent telescope of argument types

Constructor body context extension order (outermost to innermost, each group in declaration order):

```
self : D | formal index slots | params | field₀ | field₁ | ...
```

The formal index slots exist only to keep the internal de Bruijn layout compatible with the family telescope. Constructor field types and result-index expressions must not refer to these slots directly; a varying index needed by a constructor must instead be represented by an explicit constructor field.

In argument type position `k`, `self` is at `Var(n + m + k)`, parameters occupy `Var(k..k+m)`, and the `k` preceding fields occupy `Var(0..k)`. The same formula is used when checking or inferring a constructor application; inference requires `m = 0`, so it specializes to `Var(n + k)`.

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

The implemented conversion relation is semantic structural comparison with the specific η-cases below in `nbe::conv`. Operands must be well-typed in the same logical context, with free neutral levels below the supplied depth. Comparing `normalize` outputs syntactically is not equivalent: quotation does not η-expand neutrals or normalize universe-level syntax. Inductive definitions have nominal identity (the same `TermId`), not structural identity.

### 2.1 Computation Rules

| Rule | Statement | Name |
|---|---|---|
| **β-red** | `(λ. b) a ≡ b[a/x]` | Beta reduction |
| **β-fst** | `fst (a, b) ≡ a` | Pair projection |
| **β-snd** | `snd (a, b) ≡ b` | Pair projection |
| **ι-red** | `case (K a₁…aᵣ) {…; bᵢ ⇒ eᵢ; …} ≡ eᵢ (interleave(a, ih))` | Constructor reduction (iota) |
| **Ann-erase** | `(m : A) ≡ m` | Ascription erasure |

Here `interleave(a, ih)` is an argument list, not a tuple argument: each field `aⱼ` is immediately followed by `ihⱼ` exactly when it is recursive, where `ihⱼ = case_reduce(motive, branches, aⱼ)`. For recursive flags `[true, false, true]`, the branch application is `eᵢ a₁ ih₁ a₂ a₃ ih₃`.

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
| **Con-cong** | same `def`, same `idx`, equal argument and index list lengths, args pairwise conv, indices pairwise conv ⟹ `Con ≡ Con`; the indices comparison is vacuous for values produced by checked evaluation |
| **Neut-eq** | same `level`, same spine length, elim-by-elim conversion ⟹ `Neut ≡ Neut` |

### 2.3 η-Rules

| Rule | Statement |
|---|---|
| **η-fun** | `f ≡ λx. f x` for fresh `x` (Lam ≡ Neut: compare body with application of neutral to fresh var) |
| **η-pair** | `(fst p, snd p) ≡ p` (Pair ≡ Neut: compare projections) |

---

## 3. Bidirectional Type System

The kernel uses bidirectional typing: checking mode (⇐) and inference mode (⇒).

### 3.1 Context

A typing context `Γ` is a sequence of bound variables with their types:

```
Γ = x₁:A₁, x₂:A₂, ..., xₙ:Aₙ
```

Internally: `Ctx { types: Option<EnvId>, env: Option<EnvId>, depth: n }`. Both environments are linked stacks accessed by de Bruijn index (0 = newest). Ordinary binders map to neutral values carrying absolute levels; formation also installs a concrete family value for `self` and permutes signature locals into body order.

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
(parameters must be empty because bare constructor syntax provides no expected
family type from which parameter values could be recovered; otherwise inference
fails with CannotInferParameters)
Kᵢ is the i-th constructor with fields [F₁,...,Fₖ]
Γ ⊢ aⱼ ⇐ Fⱼ[prev_args/self/params/formal-index-slots]   for j = 1..k
(the formal index slots are layout placeholders and cannot occur in Fⱼ)
computed indices = eval(con_def.indices) with args bound
─────────────────────────────────────────────────────────────
Γ ⊢ Con { def: D, idx: i, args: [a₁,...,aₖ], ... } ⇒ D indices...
```

Both constructor paths validate the declaration, constructor number, and exact field count. `Term::Con.indices` may be empty; otherwise it must contain exactly all result indices, typecheck in the caller context against the instantiated index telescope, and convert pairwise to the computed values.

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
motive : Π(x : D p₁…pₘ i₁…iₙ). Type ℓ  (uniform over fresh indices)
the motive term may be a lambda or any inferable term with this Pi type
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
6. Exactly n result index expressions are well-typed against the index telescope,
   instantiated with parameters and preceding computed result indices
7. Field types and result expressions do not refer to formal index slots
8. Case elimination of a currently forming declaration (including an enclosing
   one) is rejected with UnsupportedSelfElimination
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
- For Con: preserve `def` and `idx`, quote each field and any legacy index payload (empty after checked evaluation)

### 4.6 Full Normalization

```
normalize(t) = quote(eval(t, empty_env), 0)
```

This entry point assumes a closed, well-typed term; it does not perform type checking. Quotation preserves nominal definition references and universe-level syntax.

### 4.7 Closure Instantiation

```
inst(Closure(env, body), arg) = eval(body, env ∪ {arg})
```

---

## 5. Cumulativity

Universe levels support cumulativity via `leq_level`:

```
Γ ⊢ t ⇒ Type ℓ₁    leq_level(ℓ₁, ℓ₂)
─────────────────────────────────────
Γ ⊢ t ⇐ Type ℓ₂

In particular: Γ ⊢ Type ℓ ⇐ Type L requires leq_level(suc ℓ, L).
```

Level comparison is a conservative decidable approximation, not the complete semantic ordering of symbolic `max` expressions:
- Constant offsets are compared directly
- Each level variable's individual offset must be ≤ the corresponding variable in the target

Thus `Type 0 : Type 1`, but not `Type 0 : Type 0`. Cumulativity is the universe fallback in checking; it is not recursive subtyping of Pi or Sigma types.

---

## 6. Inductive Types

### 6.1 Formation

An inductive type `D` is declared with:
- Universe level `ℓ`
- Parameter telescope `p₁:A₁, ..., pₘ:Aₘ`
- Index telescope `i₁:I₁(p₁..pₘ), ..., iₙ:Iₙ(p₁..pₘ, i₁..iₙ₋₁)`
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
Γ_fields ⊢ eₖ ⇐ Iₖ(params, e₁, ..., eₖ₋₁)
each field universe ℓⱼ satisfies leq_level(ℓⱼ, ℓ)
─────────────────────────────────────────────
Kⱼ : Π params. Π f₁:B₁. ... Π fᵣ:Bᵣ. D params e₁...eₙ
```

Formal index slots are present in the internal constructor-body layout but are not binders in the constructor's introduction telescope. Field types may refer to `self` only under the recurrence restrictions in §6.3 and may depend on parameters and preceding fields. Result-index expressions may depend on parameters and all fields, but must not contain the distinguished `self` variable. Neither may refer directly to the formal index slots. Any varying index required by a constructor must be carried by an explicit field. Result index expressions are evaluated after all fields are bound and determine the indices of the constructed family value.

The displayed type is the general constructor schema: both parameters and computed result indices are applied to `D`. In checking mode, parameter values are recovered from the expected type, and computed indices are compared with its index arguments; `check` returns success or an error, not a synthesized result type. In inference mode, the kernel requires the parameter telescope to be empty, so the same result specializes to `D e₁...eₙ`; a parameterized constructor cannot be inferred without an expected type.

### 6.3 Strict Positivity

For each constructor argument at position `k`:

1. If the inductive type `D` does not occur in the argument type: **non-recursive** (`Recurrence::None`)
2. If `D` occurs, it must be a **saturated direct application**:
   - Head is `self` (the inductive type being defined)
   - Applied to exactly `params + indices` arguments
   - All arguments are self-free (do not reference `D`)
   - Parameter arguments must be the original parameters (identity substitution)
3. The recursive metadata vector must have exactly one flag per field, and each flag must match the structural recurrence analysis exactly
4. Result index expressions must not contain the distinguished `self` variable (located at `Var(n + m + r)` after all `r` fields are bound)

This is a conservative subset: nested inductives, function types containing `D`, and `D` inside Sigma types are all rejected.

### 6.4 Elimination (Case Analysis)

```
case t as x in P { K₁ b₁ ⇒ e₁ ; ... ; Kₖ bₖ ⇒ eₖ } : P t
```

The motive `P` is a unary function from the inductive type to a universe. Syntactically it may be a lambda `λx. body`, whose body is inferred to inhabit a universe under `x`, or any other inferable term whose type is definitionally `Π(x : D p₁...pₘ i₁...iₙ). Type ℓ` (for example, a variable or neutral motive). For indexed families, the checker validates it uniformly across fresh index variables, but the runtime ABI still passes only the target value; indices are not separate motive arguments. A neutral motive fixed to one concrete indexed fiber can pass the initial check but fail the fresh-index check; having the Pi type for the original target alone is insufficient. This is a restricted encoding rather than a general `Π indices. D params indices → Type` runtime recursor.

Branch type for constructor `Kⱼ` with fields `f₁,...,fᵣ` and recursive flags:

```
Π(f₁:B₁). [ih₁:P(f₁) if recursive] ... Π(fᵣ:Bᵣ). [ihᵣ:P(fᵣ) if recursive]. P(Kⱼ f₁...fᵣ)
```

### 6.5 Computational Behavior

- **iota-reduction**: apply the selected branch to `interleave(a, ih)` as defined in §2.1, retaining the same motive and branches in every recursive call
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
