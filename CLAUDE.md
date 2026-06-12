# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project overview

A Lean 4 / Mathlib formalization project about **generalised Beauville groups**: groups equipped
with multiple "generating pairs" whose associated Σ-sets are pairwise disjoint (the group-theoretic
condition behind Beauville surfaces).

## Commands

- Build everything: `lake build`
- Build a single module: `lake build GenBeauGrp.Basic` (or `GenBeauGrp.SigmaSet`, etc.)
- Type-check/elaborate a single file directly: `lake env lean GenBeauGrp/Basic.lean`
- Fetch precompiled Mathlib `.olean` cache (do this after cloning or after bumping the Mathlib `rev`
  in `lakefile.toml`, otherwise Mathlib must be rebuilt from source): `lake exe cache get`

Lean toolchain and Mathlib version are pinned: `lean-toolchain` sets `leanprover/lean4:v4.30.0-rc2`,
and `lakefile.toml` pins `mathlib` to `rev = "v4.30.0-rc2"`. Keep these in sync if either is updated.

## Architecture

- `GenBeauGrp.lean` — root library file; only modules `import`ed here are part of the public
  `GenBeauGrp` namespace's import graph. It currently imports only `GenBeauGrp.Basic` and
  `GenBeauGrp.SigmaSet`. (`lake build` with no args still type-checks every `.lean` file under
  `GenBeauGrp/` as part of the `GenBeauGrp` lean_lib target, regardless of whether it's imported here.)

- `GenBeauGrp/Basic.lean` — core structures:
  - `GeneratingPair G` (for `[Group G]`): bundles `x y : G` with a proof
    `Subgroup.closure {x, y} = ⊤`, i.e. `x, y` generate `G`.
  - `AddGeneratingPair G` — additive analogue for `[AddGroup G]`.

- `GenBeauGrp/SigmaSet.lean` — `sigmaSet x y : Set G`: the union of all conjugates of the cyclic
  subgroups `⟨x⟩`, `⟨y⟩`, `⟨x*y⟩`. Two generating pairs yield a Beauville structure iff their
  Σ-sets intersect only at the identity.

- `GenBeauGrp/Structures.lean` — `GeneralisedBeauvilleStructure G`: an indexed family
  `pairs : ι → GeneratingPair G` over a `Fintype ι`, with the condition
  `(⋂ i, sigmaSet (pairs i).x (pairs i).y) = {1}` (the Σ-sets meet only at the identity). Imports
  `Basic` and `SigmaSet` and type-checks, but is **not yet imported into `GenBeauGrp.lean`**, so it is
  outside the public import graph (still type-checked by a bare `lake build`).

- `GenBeauGrp/Examples.lean` — scratch examples and lemmas-in-progress (generating pairs for `ℤ`,
  `ℤ × ℤ`, products of cyclic groups, permutation helpers `s`/`c` on `Equiv.Perm (Fin n)`). Not yet
  imported into `GenBeauGrp.lean`; treat as exploratory/unfinished.

## CI

`.github/workflows/lean_action_ci.yml` runs on every push/PR via `leanprover/lean-action`, builds the
project, and generates docs via `docgen-action`.
