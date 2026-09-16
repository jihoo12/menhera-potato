# Differential Testing: `rock` vs Agda

Per [`AGENTS.md`](../../AGENTS.md) §3 and §3.1, every change to the trusted kernel must be differentially tested against a reference implementation.

We use **Agda 2.8.0** as our reference implementation.

## 1. Syntax Translation Table

| `rock` Syntax (`Term`) | Agda Surface Syntax | Meaning |
|---|---|---|
| `Term::Var(i)` | de Bruijn index / named variable | Local variable |
| `Term::Lam(body)` | `\ x -> body` | Lambda abstraction |
| `Term::Pi(dom, cod)` | `(x : dom) -> cod` | Dependent function type (Π) |
| `Term::App(f, a)` | `f a` | Function application |
| `Term::Univ(l)` | `Set ℓ` | Universe |
| `Term::Ann(tm, ty)` | `(tm : ty)` | Type ascription |
| `Term::Sigma(dom, cod)` | `Σ dom (\ x -> cod)` | Dependent pair type (Σ) |
| `Term::Pair(a, b)` | `(a , b)` | Pair constructor |
| `Term::Fst(p)` | `p .fst` | First projection |
| `Term::Snd(p)` | `p .snd` | Second projection |
| `Term::Inductive { level, constructors }` | `data D : Set ℓ where K₁ : ... \| K₂ : ...` | General inductive type definition |
| `Term::Con { def, idx, args }` | `K a₁ a₂ ...` | Constructor application |
| `Term::Case { target, motive, branches }` | `case t of { K₁ => b₁ ; ... ; Kn => bn }` | Case analysis / elimination |

## 2. Running Differential Tests

Run cargo integration tests:
```bash
cargo test --test differential_test
```

This harness executes Agda 2.8.0 (`agda --no-libraries`) on all cases under `tests/differential/cases/`, asserting:
- Positive cases typecheck in both Agda and `rock` and reduce to matching normal forms.
- Negative cases are rejected by both Agda and `rock`.

## Structural recurrence hardening

The rollback hardening patch uses the structural-check exception in AGENTS.md
§5 stage 0. `recursive: Vec<bool>` and a nested definition's de Bruijn offsets
have no Agda surface-syntax equivalents; these representation invariants are
covered by `tests/rollback_audit.rs` and `tests/kernel.rs`. No new computation
rule is introduced. Existing Agda comparisons still run with `cargo test`.

Rock deliberately rejects positive function, Sigma, and nested recursion:
its evaluator can recurse only on a direct constructor argument. Agda supports
more general recursion, so agreement on rejection of these unsupported shapes
would not be an appropriate differential assertion. Direct Nat/Vec formation
and existing negative positivity cases remain covered by the Agda harness.

## Branch telescope comparison

`rollback_audit_inductive` pairs A1–A4, B1–B2, and E3 with the
`Branch*.agda` files through `branch_reference.rs`. `BranchTelescope.agda`
spells out the dependent eliminator with interleaved field/IH binders and
checks `(2, 5)`, `(5, 2)`, and the dependent identity result by `refl`.
The negative siblings check exchanged child/IH, exchanged Bool/IH,
wrong-child dependent IH, and a missing IH binder. The Rust terms and their
original acceptance/rejection/normalization assertions remain in the audit.

After the telescope and constructor-argument context corrections, A1–A4,
B1–B2, and E3 agree with Agda. B1 previously normalized correctly but failed
in rock while Agda accepted it: constructor checking extended the source
context after the first argument, so the unchanged second argument index
resolved to an IH. Both constructor paths now keep the caller context fixed
and extend only the environment that instantiates stored field types.
The indexed-family audit failures are now covered by the indexed signature correction below.

## Indexed signature and constructor scopes

`IndexedScopes.agda` corresponds to the C audit fixtures and
`tests/indexed_family.rs`: Tagged constructor use and elimination, an index
whose type is a parameter, two dependent parameters/indices, dependent result
indices, and Chain recursion. Computation is checked by Agda `refl` and Rust
normalization. `IndexedBadResult`, `IndexedBadScope`,
`IndexedBadDependentResult`, and `IndexedBadMotive` are rejection comparisons;
all are executed, and diagnostic checks exclude unrelated compiler failures.

The declaration signature is exactly `Π params. Π indices. Type level`.
Parameter type j sees the caller plus j earlier parameters; index type j sees
all parameters plus j earlier indices. `form_family` checks this telescope
before evaluating it. It instantiates those checked types with semantic locals
and explicitly permutes the same values into the legacy constructor layout.
No signature TermId is evaluated as constructor-body syntax.

For p parameters, i indices, and k previous constructor fields, body syntax is:

| Variable | de Bruijn index |
|---|---|
| Earlier field a_j | k - 1 - j |
| Parameter p_j | k + p - 1 - j |
| Formal index i_j (reserved slot) | k + p + i - 1 - j |
| Self (unapplied family) | k + p + i |
| Caller variable Γ_j | k + p + i + 1 + j |

Result expressions use the body context after all fields. Their expected types
are evaluated separately in `caller + parameters + earlier result values`.
The result count must equal the declared index count. Supplied `Con.indices`
are caller syntax; they are checked before evaluation and compared with the
computed results. Both constructor APIs validate the definition first.

The current representation has these explicit, conservative limits:

- Formal index slots are not constructor arguments and the evaluator never
  passes them to branches. References to them are rejected; an index that
  varies with a constructor must be an explicit field (as in Vec or Chain).
  Agda may elaborate implicit fields; there is no equivalent omitted-field
  raw representation to compare, so this invariant has a Rust regression.
- `Con` stores no parameter arguments. Parameterized constructors require an
  expected type or `Ann`; inference returns `CannotInferParameters` rather
  than treating parameter TYPE expressions as their values.
- Runtime motives remain unary. With parameters fixed, an indexed motive is
  checked at arbitrary fresh indices as well as the target fiber. Its checked
  value is requoted into the larger context before this check. This supports
  index-implicit unary motives; explicit index-taking motives would need a
  separately reviewed AST/evaluator extension. A motive confined to one fiber
  is rejected, in agreement with `IndexedBadMotive.agda`.

No NbE computation or conversion implementation was changed. Definition
validation is currently repeated at constructor/case entry points; no cache
or arena-identity refactor is included in this patch.
