# Proof obligations and status

This ledger tracks evidence, not aspirations. The specification was migrated from an audited implementation description at commit `84fd75e3e4ef7b5a64234aa07b534e8c773283a4`. No complete proof of global kernel soundness is supplied by that audit or by this migration. Existing Rust and Agda tests are regression evidence only.

## Status vocabulary

- **Open:** no complete proof artifact is recorded.
- **Draft:** a statement or partial argument exists; gaps remain.
- **Proved (written):** a complete mathematical proof and its discharged dependencies are linked.
- **Proved (mechanized):** checked proof files, checker version, commands/results, and assumptions are linked.
- **Conditional:** the argument depends on an explicitly unresolved assumption; it does not pass the implementation gate.
- **Invalidated:** a rule change has made an earlier proof inapplicable.

Implementation and test status must be recorded separately from proof status. Do not change a row to proved without an inspectable proof.

## Baseline obligations

All rows below are **Open**. These are proof tasks, not established theorems; their precise statements and any required declarative relation must be supplied in the proof artifacts.

| ID | Required statement / scope | Main specification sections | Proof artifact |
|---|---|---|---|
| SCOPE | Weakening, substitution, and environment well-formedness preserve scope and typing; signature/body permutation preserves interpretation | §1, §3, §7 | Not supplied |
| LEVEL | Level normalization/equality and the specified ordering are sound for the chosen level semantics; successor and max preserve needed properties | §1.1, §5 | Not supplied |
| FORM | Accepted family declarations and constructor telescopes are well-formed; closure, saturation, universes, positivity and result-index restrictions are sufficient for the claimed fragment | §3.2, §6.1–6.3 | Not supplied |
| CONV | Successful semantic conversion entails equality in an independently stated logical relation at a common type/context, including the implemented η-cases and nominal identities | §2, §4 | Not supplied |
| TYPE | Successful inference/checking entails the corresponding logical typing judgment, using CONV and the relevant formation lemmas | §3, §5, §6 | Not supplied |
| RED | β, projections and interleaved ι computation preserve typing, including indexed motives and recursive IHs | §2.1, §6.4–6.5 | Not supplied |
| NBE | Evaluation and quotation preserve their semantic/typing relation, with correct binder depths and annotation erasure | §4, §7 | Not supplied |
| TERM | Termination of evaluation, conversion and type checking on their specified inputs; account for recursive calls and formation guards | §2–§6 | Not supplied |
| CANON | Canonicity for the specified closed types and consistency (e.g. no closed inhabitant of a suitable empty family), with explicit dependencies | §3–§6 | Not supplied |
| REFINE | Rust operations refine the mathematical model under explicit arena validity, integer-bound and resource assumptions | §1.1, §4, §7 | Not supplied |

Typical dependencies include scope/level lemmas before typing and conversion arguments, family formation and motive lemmas before ι-preservation, and normalization/canonicity arguments before consistency. This is guidance for planning, not a proof dependency graph already shown to be acyclic.

The logical target of TYPE and CONV must be defined independently of the implementation's success result; defining typing as “the checker accepts” would make soundness circular. Preservation alone does not establish normalization, canonicity or consistency.

## Feature proof record

For each feature, create `spec/proofs/<feature>.md` and add a ledger entry with:

1. Feature name and exact specification revision/rule identifiers.
2. Status of specification, proof, implementation and validation, separately.
3. Definitions and theorem statements, including quantifiers and side conditions.
4. Dependencies: proved lemmas with links, external results with matching hypotheses, and open obligations.
5. Full proof, including changed and interacting cases; identify the induction measure or semantic model.
6. Representation/refinement argument and planned rule → theorem → function mapping.
7. Counterexamples considered and specification-derived test cases.
8. If mechanized: checker version, command, result, and any axioms or trusted components.
9. Remaining limitations. Do not mark implementation-ready until the required proof dependencies are discharged.

If a baseline obligation blocks a feature, prove the needed baseline fragment first and state its precise scope. Do not mark the entire baseline row proved for a fragment-only result.

## Migration status

- Canonical specification: [formal_system.md](formal_system.md).
- Development policy: [AGENTS.md](../AGENTS.md).
- Production semantics changed by this migration: none.
- New completed soundness proofs supplied by this migration: none.
