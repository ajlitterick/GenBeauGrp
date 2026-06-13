import GenBeauGrp.SigmaSet
import Mathlib.Algebra.Group.Conj

/-- In a commutative group conjugation is trivial, so the Σ-set of `(x, y)` collapses to the
plain union of the three cyclic subgroups `⟨x⟩`, `⟨y⟩`, `⟨x*y⟩`. -/
theorem sigmaSet_of_comm {G : Type*} [CommGroup G] (x y : G) :
    sigmaSet x y =
      ↑(Subgroup.zpowers x) ∪ ↑(Subgroup.zpowers y) ∪ ↑(Subgroup.zpowers (x * y)) := by
  ext g
  simp only [sigmaSet, Group.mem_conjugatesOfSet_iff, isConj_iff_eq, exists_eq_right]

/-- The identity lies in every Σ-set. -/
theorem one_mem_sigmaSet {G : Type*} [Group G] (x y : G) : (1 : G) ∈ sigmaSet x y :=
  Group.subset_conjugatesOfSet (Or.inl (Or.inl (one_mem _)))

/-- In a commutative group, if `g ∈ Σ(x, y)` then the whole cyclic subgroup `⟨g⟩` lies in
`Σ(x, y)` (because `g` lies in one of the three constituent subgroups). -/
theorem zpowers_subset_sigmaSet {G : Type*} [CommGroup G] {g x y : G} (hg : g ∈ sigmaSet x y) :
    (↑(Subgroup.zpowers g) : Set G) ⊆ sigmaSet x y := by
  rw [sigmaSet_of_comm] at hg ⊢
  rcases hg with (h | h) | h
  · exact fun z hz => Or.inl (Or.inl (Subgroup.zpowers_le.mpr h hz))
  · exact fun z hz => Or.inl (Or.inr (Subgroup.zpowers_le.mpr h hz))
  · exact fun z hz => Or.inr (Subgroup.zpowers_le.mpr h hz)
