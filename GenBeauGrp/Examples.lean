import GenBeauGrp.Basic

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

example
  (G₁ G₂ : Type*) [CommGroup G₁] [CommGroup G₂] [IsCyclic G₁] [IsCyclic G₂] : GeneratingPair (G₁ × G₂) := by
    classical
    let h₁ := IsCyclic.exists_zpow_surjective
    let h₂ := IsCyclic.exists_zpow_surjective (G := G₂)
    let ⟨a,h⟩ := h₁
    exact ⟨ (g₁,1), (1,g₂), by
      apply top_unique
      intro ⟨a,b⟩ _
      apply Subgroup.mem_closure_pair.mpr
      use a, b
      norm_num
    ⟩



#print IsCyclic.exists_zpow_surjective
#check IsCyclic.exists_zpow_surjective

def s {n : ℕ} (hn : 2 < n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨ 0, Nat.zero_lt_of_lt hn⟩ ⟨1, Nat.lt_of_add_left_lt hn⟩

def c (n : ℕ) (hn : 2 < n) : Equiv.Perm (Fin n) := Fin.cycleRange ⟨ n-1, by omega⟩
