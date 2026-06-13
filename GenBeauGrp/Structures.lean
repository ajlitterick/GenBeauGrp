import GenBeauGrp.Basic
import GenBeauGrp.SigmaSet


structure GeneralisedBeauvilleStructure (G : Type*) [Group G] where
  (ι : Type*)
  [fintype_ι : Fintype ι]
  (pairs : ι → GeneratingPair G)
  (inter_sigmaSet_eq_one :
    (⋂ i, sigmaSet (pairs i).x (pairs i).y) = {1})

attribute [instance] GeneralisedBeauvilleStructure.fintype_ι

/-- The **dimension** of a generalised Beauville structure: the number of Σ-sets involved,
i.e. the cardinality of the indexing type. -/
def GeneralisedBeauvilleStructure.dimension {G : Type*} [Group G]
    (B : GeneralisedBeauvilleStructure G) : ℕ :=
  Fintype.card B.ι

/-- A generalised Beauville structure is **primitive** if no proper subcollection of its
Σ-sets is itself a generalised Beauville structure. Equivalently, for every proper subset `S`
of the index type the corresponding Σ-sets meet in more than just the identity (so removing any
indices breaks the defining intersection condition). -/
def GeneralisedBeauvilleStructure.IsPrimitive {G : Type*} [Group G]
    (B : GeneralisedBeauvilleStructure G) : Prop :=
  ∀ S : Finset B.ι, S ≠ Finset.univ →
    (⋂ i ∈ S, sigmaSet (B.pairs i).x (B.pairs i).y) ≠ {1}

/-- **Existence of a Σ-set not containing a given set.** If `X ⊆ G` contains a non-identity
element, then in any generalised Beauville structure `B` of `G` some Σ-set fails to contain `X`.
(If every Σ-set contained `X`, its non-identity element would lie in `⋂ᵢ Σᵢ = {1}`.) -/
theorem GeneralisedBeauvilleStructure.exists_sigmaSet_not_subset {G : Type*} [Group G]
    (B : GeneralisedBeauvilleStructure G) {X : Set G} (hX : ∃ g ∈ X, g ≠ 1) :
    ∃ i, ¬ X ⊆ sigmaSet (B.pairs i).x (B.pairs i).y := by
  obtain ⟨g, hgX, hg1⟩ := hX
  by_contra h
  simp only [not_exists, not_not] at h
  have hmem : g ∈ ⋂ i, sigmaSet (B.pairs i).x (B.pairs i).y :=
    Set.mem_iInter.mpr fun i => h i hgX
  rw [B.inter_sigmaSet_eq_one, Set.mem_singleton_iff] at hmem
  exact hg1 hmem
