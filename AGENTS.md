# Repository instructions

These instructions apply to the entire repository.

## Development order: specification → proof → implementation → validation

This project is a Rust MLTT kernel (`rock`). Do not begin a new feature by editing production code. For every feature or semantic change, complete the following stages in order:

1. **Specify.** Read `spec/formal_system.md` and `spec/proof_obligations.md`. Define the intended change in the formal system first: syntax and scope, formation/introduction/elimination rules, conversion and computation rules, universe constraints, and representation invariants. Include accepted examples, rejected examples, and compatibility with existing terms. Label proposed rules as proposed/unimplemented until the later stages finish; never describe them as existing behavior.
2. **Prove.** Write a proof artifact under `spec/proofs/<feature>.md` (or a mechanized proof with documentation). State the exact theorem, assumptions, affected rules, dependencies, and proof cases. Discharge the soundness obligations affected by the change before implementing it. Update the status ledger in `spec/proof_obligations.md`.
3. **Implement.** Only after the proof gate is satisfied, translate the specified and proved rules into `src/`. Record a rule → theorem → function mapping. If implementation requires different semantics, return to stages 1 and 2 first.
4. **Validate.** Add positive, negative, and computation regression tests derived from the specification. Run relevant tests and the full suite for kernel changes. Audit the final specification/proof/code correspondence and update implementation status.

Stage completion must be visible in the artifacts and change description. Prefer separate commits for specification, proof, and implementation when practical; commit ordering alone is not evidence of a completed proof.

## What satisfies the proof gate

- A complete written mathematical proof is acceptable; mechanization is encouraged. Identify which form is supplied.
- A proof must state the property actually established: algorithmic typing soundness, conversion soundness, preservation, termination, canonicity, or consistency. These are distinct claims.
- Cover relevant interactions with existing rules and all cases introduced or changed. List supporting lemmas with links and exact assumptions.
- A sketch, TODO, unchecked mechanized file, admitted goal, circular argument, test result, source audit, or citation alone is not a completed proof.
- A citation may supply a lemma only with its exact statement, relevant hypotheses, and an argument that those hypotheses and the embedding apply to this kernel.
- Open dependencies must remain visible. An extension theorem conditional on an unproved baseline theorem does not establish unconditional soundness and does not satisfy the implementation gate. Close the needed dependencies first; do not bypass the gate because existing code predates this policy.
- If blocked, continue specification and proof work, record the precise unresolved obligation and a counterexample if known, and report the blocker. Do not implement the feature or relabel the gap as proved.
- Existing implementation is an audited baseline, not a globally proved kernel. This policy does not retroactively certify it.

For semantic bug fixes, specify the corrected rule and establish the relevant correctness argument before editing code. For behavior-preserving refactors or optimizations, identify the existing rules and prove preservation of their observable behavior before implementation. Pure editorial changes, documentation moves, formatting, and changes with no semantic effect need an explicit no-semantic-change explanation, not a fabricated metatheorem. These exceptions must not be used to ship a feature first.

## Specification discipline

- `spec/formal_system.md` is the canonical formal-system document; `memo/` holds informal notes and `audit/` holds historical findings.
- Do not change the specification merely to excuse a code bug. Resolve discrepancies against the intended, justified rules and document the decision.
- Preserve the distinction between logical rules, algorithmic restrictions, and Rust representation details.
- Use exact binder order and substitution conventions. Distinguish de Bruijn indices from levels, family parameters from formal index slots, and computed indices from erased annotations.
- Keep side conditions explicit: declared universes, closure, saturation, positivity, recursive metadata, motive uniformity, and formation-time elimination restrictions.
- Do not silently assume general MLTT, Lean, or Agda features exist here.
- Preserve nominal inductive identity unless a new identity model is specified and proved.
- Mathematical assumptions about unbounded naturals do not justify Rust integer overflow or arena misuse; state machine-level preconditions and implementation obligations.
- Keep proposed, proved, implemented, and tested statuses separate. Update dependent proofs when a rule changes.

## Validation and reporting

From the repository root:

```sh
cargo fmt --check
cargo test
```

For changes covered by differential tests, also follow `tests/differential/README.md` and run:

```sh
cargo test --test differential_test
```

The differential harness uses Agda 2.8.0. Report whether Agda actually ran; missing dependencies or skipped checks are not passing results. Test evidence supplements proofs and never substitutes for them.

Each completed semantic change must report:
- specification sections and proposed/implemented status;
- theorem/proof paths, assumptions, and dependency status;
- implementation functions corresponding to those rules;
- tests and commands actually executed, failures/skips, and remaining limitations.

For documentation-only work, verify links, paths, and consistency; do not claim Rust or Agda tests were run if they were not.
