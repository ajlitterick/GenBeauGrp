import GenBeauGrp.Basic
import GenBeauGrp.SigmaSet


structure GeneralisedBeauvilleStructure (G : Type*) [Group G] where
  (ι : Type*)
  [fintype_ι : Fintype ι]
  (pairs : ι → GeneratingPair G)
  (inter_sigmaSet_eq_one :
    (⋂ i, sigmaSet (pairs i).x (pairs i).y) = {1})
