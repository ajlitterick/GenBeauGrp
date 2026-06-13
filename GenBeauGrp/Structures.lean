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
