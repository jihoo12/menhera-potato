# Mechanized baseline fragments

These modules prove statements about independently defined raw kernel syntax.
They are separate from the Rust/Agda differential examples under `tests/`.
See the [renaming](../scope-renaming.md) and
[substitution](../scope-substitution.md) artifacts for the precise boundaries.

From the repository root, using Agda 2.8.0 without a standard library:

```sh
agda --no-libraries --safe --without-K -i spec/proofs/agda spec/proofs/agda/Scope/Examples.agda
```

`Examples` imports `Substitution`, `Renaming` and `Syntax`, so this checks
both complete fragments.
To force checking from source without using cached interfaces:

```sh
agda --ignore-interfaces --no-libraries --safe --without-K -i spec/proofs/agda spec/proofs/agda/Scope/Examples.agda
```

`Syntax` owns raw terms and the extrinsic scope predicate; `Renaming` owns
index-map lifting, renaming, its scope theorem and weakening; `Substitution`
owns simultaneous substitution, its binder lifting and scope theorem; `Examples`
checks binder-sensitive positive, negative and computation examples.
Universe labels are parameters, not Agda universes interpreted as kernel types.
Single-variable instantiation can next reuse `subst-scoped` without expanding
into typing, inductive declarations or semantic values.
