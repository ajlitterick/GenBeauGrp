# GenBeauGrp

A [Lean 4](https://leanprover.github.io/) / [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of **generalised Beauville groups**.

## Overview

A *Beauville surface* is built from a pair of curves with a free action of a finite group `G`.
The geometry is controlled entirely by group theory: `G` must carry two *generating pairs* whose
associated **Σ-sets** meet only at the identity. This project formalizes that group-theoretic data
and generalises it to an arbitrary finite family of generating pairs.

The central definitions are:

- A **generating pair** `(x, y)` of `G`: two elements with `⟨x, y⟩ = G`.
- The **Σ-set** of a pair, `sigmaSet x y`: the union of all conjugates of the cyclic subgroups
  `⟨x⟩`, `⟨y⟩`, and `⟨x·y⟩`. Two pairs give a Beauville structure exactly when their Σ-sets
  intersect only in `{1}`.
- A **generalised Beauville structure**: an indexed family of generating pairs `pairs : ι → GeneratingPair G`
  over a finite `ι`, whose Σ-sets satisfy `⋂ᵢ sigmaSet (pairs i).x (pairs i).y = {1}`.

## Module layout

| File | Contents |
| --- | --- |
| `GenBeauGrp.lean` | Root library file; defines the public import graph (currently `Basic`, `SigmaSet`). |
| `GenBeauGrp/Basic.lean` | `GeneratingPair G` and its additive analogue `AddGeneratingPair G`. |
| `GenBeauGrp/SigmaSet.lean` | `sigmaSet x y` — the union of conjugates of `⟨x⟩`, `⟨y⟩`, `⟨x·y⟩`. |
| `GenBeauGrp/Structures.lean` | `GeneralisedBeauvilleStructure G` — a finite family of pairs with disjoint Σ-sets. |
| `GenBeauGrp/Examples.lean` | Worked examples: generating pairs for `ℤ`, `ℤ × ℤ`, products of cyclic groups, and the symmetric group `Equiv.Perm (Fin n)` (the `n`-cycle plus an adjacent transposition). |

`Structures.lean` and `Examples.lean` type-check but are not yet imported into `GenBeauGrp.lean`, so
they sit outside the public import graph (a bare `lake build` still checks them).

## Building

This project pins a specific Lean toolchain and Mathlib revision (both `v4.30.0-rc2`), kept in sync
between `lean-toolchain` and `lakefile.toml`.

```sh
# Fetch the precompiled Mathlib cache (do this after cloning, or after bumping the Mathlib rev,
# otherwise Mathlib is rebuilt from source — slow).
lake exe cache get

# Build everything.
lake build

# Build a single module.
lake build GenBeauGrp.Basic

# Type-check a single file directly.
lake env lean GenBeauGrp/Basic.lean
```

## Continuous integration

`.github/workflows/lean_action_ci.yml` runs on every push and pull request via
[`leanprover/lean-action`](https://github.com/leanprover/lean-action): it builds the project and
generates documentation with `docgen-action`.
