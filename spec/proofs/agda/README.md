# Mechanized baseline fragments

These modules prove statements about independently defined raw kernel syntax.
They are separate from the Rust/Agda differential examples under `tests/`.
Start with [the SCOPE artifact](../scope-renaming.md) for the precise boundary.

From the repository root, using Agda 2.8.0 without a standard library:

```sh
agda --no-libraries --safe --without-K -i spec/proofs/agda spec/proofs/agda/Scope/Examples.agda
```

`Examples` imports `Renaming` and `Syntax`, so this checks the entire fragment.
To force checking from source without using cached interfaces:

```sh
agda --ignore-interfaces --no-libraries --safe --without-K -i spec/proofs/agda spec/proofs/agda/Scope/Examples.agda
```

`Syntax` owns raw terms and the extrinsic scope predicate; `Renaming` owns
index-map lifting, renaming, its scope theorem and weakening; `Examples`
checks binder-sensitive positive, negative and computation examples.
Universe labels are parameters, not Agda universes interpreted as kernel types.
Future substitution work can depend on these modules without formalizing
inductive declarations or semantic values prematurely.
