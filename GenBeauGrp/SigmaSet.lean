import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Conj

/-- The Σ-set of a pair `(x, y)` in a group `G`: the union of all conjugates
of the cyclic subgroups `⟨x⟩`, `⟨y⟩`, `⟨x*y⟩`. Equal to
`⋃ g n, {g*x^n*g⁻¹, g*y^n*g⁻¹, g*(x*y)^n*g⁻¹}`. -/
def sigmaSet {G : Type*} [Group G] (x y : G) : Set G :=
  Group.conjugatesOfSet
    (↑(Subgroup.zpowers x) ∪ ↑(Subgroup.zpowers y)
      ∪ ↑(Subgroup.zpowers (x * y)) : Set G)

/-- Σ-sets are closed under conjugation. -/
theorem conj_mem_sigmaSet {G : Type*} [Group G] {x y g c : G} (hg : g ∈ sigmaSet x y) :
    c * g * c⁻¹ ∈ sigmaSet x y :=
  Group.conj_mem_conjugatesOfSet hg

/-- Σ-sets are closed under taking integer powers of their elements. -/
theorem zpow_mem_sigmaSet {G : Type*} [Group G] {x y g : G} (hg : g ∈ sigmaSet x y) (n : ℤ) :
    g ^ n ∈ sigmaSet x y := by
  obtain ⟨a, ha, hac⟩ := Group.mem_conjugatesOfSet_iff.mp hg
  obtain ⟨c, hc⟩ := isConj_iff.mp hac
  refine Group.mem_conjugatesOfSet_iff.mpr ⟨a ^ n, ?_, isConj_iff.mpr ⟨c, ?_⟩⟩
  · rcases ha with (ha | ha) | ha
    · exact Or.inl (Or.inl (zpow_mem ha n))
    · exact Or.inl (Or.inr (zpow_mem ha n))
    · exact Or.inr (zpow_mem ha n)
  · rw [← hc, conj_zpow]

/-- Σ-sets are closed under taking natural-number powers of their elements. -/
theorem pow_mem_sigmaSet {G : Type*} [Group G] {x y g : G} (hg : g ∈ sigmaSet x y) (n : ℕ) :
    g ^ n ∈ sigmaSet x y := by
  simpa using zpow_mem_sigmaSet hg (n : ℤ)

/-- If `g ∈ Σ(x, y)`, then the whole cyclic subgroup `⟨g⟩` lies in `Σ(x, y)`. -/
theorem zpowers_subset_sigmaSet' {G : Type*} [Group G] {x y g : G} (hg : g ∈ sigmaSet x y) :
    (↑(Subgroup.zpowers g) : Set G) ⊆ sigmaSet x y := by
  rintro z ⟨n, rfl⟩
  exact zpow_mem_sigmaSet hg n

/-- Σ-sets are closed under conjugation of subsets: if `S ⊆ Σ(x, y)`, then every conjugate of
every element of `S` also lies in `Σ(x, y)`. -/
theorem conjugatesOfSet_subset_sigmaSet {G : Type*} [Group G] {x y : G} {S : Set G}
    (hS : S ⊆ sigmaSet x y) : Group.conjugatesOfSet S ⊆ sigmaSet x y := by
  intro g hg
  obtain ⟨a, ha, hac⟩ := Group.mem_conjugatesOfSet_iff.mp hg
  obtain ⟨c, hc⟩ := isConj_iff.mp hac
  rw [← hc]
  exact conj_mem_sigmaSet (hS ha)
