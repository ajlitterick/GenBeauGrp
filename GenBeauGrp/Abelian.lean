import GenBeauGrp.SigmaSet
import Mathlib.Algebra.Group.Conj

/-- In a commutative group conjugation is trivial, so the Σ-set of `(x, y)` collapses to the
plain union of the three cyclic subgroups `⟨x⟩`, `⟨y⟩`, `⟨x*y⟩`. -/
theorem sigmaSet_of_comm {G : Type*} [CommGroup G] (x y : G) :
    sigmaSet x y =
      ↑(Subgroup.zpowers x) ∪ ↑(Subgroup.zpowers y) ∪ ↑(Subgroup.zpowers (x * y)) := by
  ext g
  simp only [sigmaSet, Group.mem_conjugatesOfSet_iff, isConj_iff_eq, exists_eq_right]
