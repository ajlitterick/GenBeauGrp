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
    have hi0 : i ≠ 0 := by
      apply Fin.ne_of_val_ne
      simp only [hi, Fin.val_zero]
      omega
    have hcyc : (c n hn).IsCycle := by rw [hc]; exact Fin.isCycle_cycleRange hi0
    have h0i : (0 : Fin n) < i := Fin.lt_def.mpr (by simp only [hi, Fin.val_zero]; omega)
    have hc0 : (c n hn) 0 = 1 := by
      rw [hc, Fin.cycleRange_of_lt h0i, zero_add]
    have hsupp : (c n hn).support = Finset.univ := by
      rw [hc, Finset.eq_univ_iff_forall]
      intro j
      rw [Equiv.Perm.mem_support]
      have hji : j ≤ i := Fin.le_def.mpr (by have := j.isLt; simp only [hi]; omega)
      rcases lt_or_eq_of_le hji with hlt | heq
      · intro h
        have h1 := Fin.coe_cycleRange_of_lt hlt
        rw [h] at h1
        omega
      · rw [heq, Fin.cycleRange_of_eq rfl]
        exact fun h => hi0 h.symm
    have e0 : (⟨0, Nat.zero_lt_of_lt hn⟩ : Fin n) = 0 := by apply Fin.ext; simp
    have e1 : (⟨1, Nat.lt_of_add_left_lt hn⟩ : Fin n) = 1 := by
      apply Fin.ext; rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < n by omega)]
    have hs : s hn = Equiv.swap (0 : Fin n) ((c n hn) 0) := by
      rw [hc0]
      unfold s
      rw [e0, e1]
    rw [hs, Set.pair_comm]
    exact Equiv.Perm.closure_cycle_adjacent_swap hcyc hsupp 0
