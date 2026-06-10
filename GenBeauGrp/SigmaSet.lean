import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-- The Σ-set of a pair `(x, y)` in a group `G`: the union of all conjugates
of the cyclic subgroups `⟨x⟩`, `⟨y⟩`, `⟨x*y⟩`. Equal to
`⋃ g n, {g*x^n*g⁻¹, g*y^n*g⁻¹, g*(x*y)^n*g⁻¹}`. -/
def sigmaSet {G : Type*} [Group G] (x y : G) : Set G :=
  Group.conjugatesOfSet
    (↑(Subgroup.zpowers x) ∪ ↑(Subgroup.zpowers y)
      ∪ ↑(Subgroup.zpowers (x * y)) : Set G)
