import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin


structure GeneratingPair (G : Type*) [Group G] where
  (x y : G)
  (generates : Subgroup.closure ({x, y} : Set G) = ⊤)

structure AddGeneratingPair (G : Type*) [AddGroup G] where
  (x y : G)
  (generates : AddSubgroup.closure ({x, y} : Set G) = ⊤)
