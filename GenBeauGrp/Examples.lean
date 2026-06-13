import GenBeauGrp.Basic
import Mathlib.GroupTheory.Perm.Closure

example : AddGeneratingPair ℤ :=
  ⟨1,-1, by
    apply top_unique
    rw [← Int.addSubgroupClosure_one]
    apply AddSubgroup.closure_mono
    rw [Set.singleton_subset_iff,Set.mem_insert_iff]
    left; rfl
  ⟩

example : AddGeneratingPair (ℤ × ℤ) :=
  ⟨(1,0), (0,1) , by
    apply top_unique
    intro ⟨a,b⟩ _
    apply AddSubgroup.mem_closure_pair.mpr
    use a, b
    norm_num
  ⟩

noncomputable example
  (G₁ G₂ : Type*) [CommGroup G₁] [CommGroup G₂] [IsCyclic G₁] [IsCyclic G₂] : GeneratingPair (G₁ × G₂) := by
    -- If g₁ generates G₁ and g₂ generates G₂, then (g₁,1) and (1,g₂) generate the product.
    let g₁ := (IsCyclic.exists_zpow_surjective (G := G₁)).choose
    let g₂ := (IsCyclic.exists_zpow_surjective (G := G₂)).choose
    have hg₁ : Function.Surjective (fun k : ℤ => g₁ ^ k) :=
      (IsCyclic.exists_zpow_surjective (G := G₁)).choose_spec
    have hg₂ : Function.Surjective (fun k : ℤ => g₂ ^ k) :=
      (IsCyclic.exists_zpow_surjective (G := G₂)).choose_spec
    exact ⟨(g₁, 1), (1, g₂), by
      apply top_unique
      intro ⟨a, b⟩ _
      apply Subgroup.mem_closure_pair.mpr
      obtain ⟨m, hm⟩ := hg₁ a
      obtain ⟨n, hn⟩ := hg₂ b
      exact ⟨m, n, by simp [hm, hn]⟩⟩

def s {n : ℕ} (hn : 2 < n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨ 0, Nat.zero_lt_of_lt hn⟩ ⟨1, Nat.lt_of_add_left_lt hn⟩

def c (n : ℕ) (hn : 2 < n) : Equiv.Perm (Fin n) := Fin.cycleRange ⟨ n-1, by omega⟩

/-- For `n > 2`, the adjacent transposition `s = (0 1)` together with the `n`-cycle
`c = (0 1 … n-1)` form a generating pair of the symmetric group `Equiv.Perm (Fin n)`:
this is the classical fact that an `n`-cycle and an adjacent transposition generate `Sₙ`. -/
def permGeneratingPair {n : ℕ} (hn : 2 < n) : GeneratingPair (Equiv.Perm (Fin n)) where
  x := s hn
  y := c n hn
  generates := by
    haveI : NeZero n := ⟨by omega⟩
    set i : Fin n := ⟨n - 1, by omega⟩ with hi
    have hc : c n hn = Fin.cycleRange i := rfl
    have hi0 : i ≠ 0 := Fin.ne_of_val_ne (by simp only [hi, Fin.val_zero]; omega)
    have h0i : (0 : Fin n) < i := Fin.lt_def.mpr (by simp only [hi, Fin.val_zero]; omega)
    have hcyc : (c n hn).IsCycle := hc ▸ Fin.isCycle_cycleRange hi0
    have hc0 : (c n hn) 0 = 1 := by rw [hc, Fin.cycleRange_of_lt h0i, zero_add]
    have hsupp : (c n hn).support = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hc, ← Equiv.Perm.sum_cycleType, Fin.cycleType_cycleRange hi0, Multiset.sum_singleton,
        Fintype.card_fin]
      have : (i : ℕ) = n - 1 := rfl
      omega
    have hs : s hn = Equiv.swap (0 : Fin n) ((c n hn) 0) := by
      rw [hc0, s, show (⟨0, Nat.zero_lt_of_lt hn⟩ : Fin n) = 0 from Fin.ext (by simp),
        show (⟨1, Nat.lt_of_add_left_lt hn⟩ : Fin n) = 1 from
          Fin.ext (by rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < n by omega)])]
    rw [hs, Set.pair_comm]
    exact Equiv.Perm.closure_cycle_adjacent_swap hcyc hsupp 0
