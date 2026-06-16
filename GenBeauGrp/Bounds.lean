import GenBeauGrp.Abelian
import GenBeauGrp.SigmaSet
import GenBeauGrp.Structures
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Data.Nat.Factorization.PrimePow

/-! # Section 3: upper bounds on `max(BSpec(G))`

This file develops the abstract machinery of Section 3 of the draft: every Σ-set contains a
"minimal subgroup" (a subgroup of prime order), and the number `k(Σ)` of conjugacy classes of
minimal subgroups contained in a Σ-set bounds the dimension of any primitive generalised
Beauville structure containing it. -/

variable {G : Type*} [Group G] [Finite G]

/-- A subgroup is **minimal** if it has prime order. -/
def IsMinimalSubgroup (H : Subgroup G) : Prop := (Nat.card H).Prime

/-- Every non-identity element generates a cyclic subgroup containing a minimal subgroup
(a subgroup of prime order, by Cauchy's theorem applied to `⟨g⟩`). -/
theorem exists_isMinimalSubgroup_le_zpowers {g : G} (hg : g ≠ 1) :
    ∃ H : Subgroup G, IsMinimalSubgroup H ∧ H ≤ Subgroup.zpowers g := by
  have hne1 : orderOf g ≠ 1 := fun h => hg (orderOf_eq_one_iff.mp h)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne1
  haveI : Fact q.Prime := ⟨hq⟩
  rw [← Nat.card_zpowers g] at hqdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  refine ⟨Subgroup.zpowers (x : G), ?_, ?_⟩
  · change (Nat.card (Subgroup.zpowers (x : G))).Prime
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
    exact hq
  · rw [Subgroup.zpowers_le]
    exact x.2

/-- The conjugacy classes of minimal subgroups contained in `S`, identified with the union
of each class (Remark 3.2). -/
def minimalClassesIn (S : Set G) : Set (Set G) :=
  { C | ∃ H : Subgroup G, IsMinimalSubgroup H ∧ C = Group.conjugatesOfSet (↑H : Set G) ∧ C ⊆ S }

/-- `k(Σ)`: the number of conjugacy classes of minimal subgroups contained in `S`. -/
noncomputable def kSigma (S : Set G) : ℕ := (minimalClassesIn S).ncard

/-- **Proposition 3.5.** For a primitive generalised Beauville structure `B` and any Σ-set
`Σᵢ₀ = Σ(B.pairs i₀)`, the dimension of `B` is at most `1 + k(Σᵢ₀)`. -/
theorem dimension_le_one_add_kSigma (B : GeneralisedBeauvilleStructure G) (hB : B.IsPrimitive)
    (i₀ : B.ι) : B.dimension ≤ 1 + kSigma (sigmaSet (B.pairs i₀).x (B.pairs i₀).y) := by
  classical
  -- For each `j`, primitivity yields a non-identity `g j` lying in every Σ-set except the
  -- `j`-th (this part is group-agnostic and mirrors `dimension_le_four`).
  have witness : ∀ j : B.ι, ∃ g : G, g ≠ 1 ∧
      (∀ k, k ≠ j → g ∈ sigmaSet (B.pairs k).x (B.pairs k).y) ∧
      g ∉ sigmaSet (B.pairs j).x (B.pairs j).y := by
    intro j
    have hproper : (Finset.univ.erase j) ≠ (Finset.univ : Finset B.ι) := by
      intro h
      have hj : j ∈ Finset.univ.erase j := by rw [h]; exact Finset.mem_univ j
      exact (Finset.mem_erase.mp hj).1 rfl
    have hne := hB _ hproper
    have h1mem : (1 : G) ∈
        ⋂ i ∈ Finset.univ.erase j, sigmaSet (B.pairs i).x (B.pairs i).y := by
      rw [Set.mem_iInter₂]
      exact fun i _ => one_mem_sigmaSet _ _
    have hex : ∃ g ∈ (⋂ i ∈ Finset.univ.erase j, sigmaSet (B.pairs i).x (B.pairs i).y),
        g ≠ 1 := by
      by_contra hc
      simp only [not_exists, not_and, not_ne_iff] at hc
      exact hne (Set.eq_singleton_iff_unique_mem.mpr ⟨h1mem, hc⟩)
    obtain ⟨g, hgX, hg1⟩ := hex
    rw [Set.mem_iInter₂] at hgX
    refine ⟨g, hg1, fun k hk => hgX k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩), ?_⟩
    intro hgj
    have hall : g ∈ ⋂ i, sigmaSet (B.pairs i).x (B.pairs i).y := by
      rw [Set.mem_iInter]
      intro k
      by_cases hk : k = j
      · subst hk; exact hgj
      · exact hgX k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
    rw [B.inter_sigmaSet_eq_one, Set.mem_singleton_iff] at hall
    exact hg1 hall
  choose g hg1 hgmem hgnot using witness
  -- For each `j`, pick a minimal subgroup `H j ≤ ⟨g j⟩`.
  choose H hHmin hHle using fun j => exists_isMinimalSubgroup_le_zpowers (hg1 j)
  set f : B.ι → Set G := fun j => Group.conjugatesOfSet (↑(H j) : Set G) with hf
  -- For `k ≠ j`, `f j ⊆ Σ_k`, since `H j ≤ ⟨g j⟩ ⊆ Σ_k` and `Σ_k` is conjugation-closed.
  have hHsub : ∀ j k, k ≠ j → (↑(H j) : Set G) ⊆ sigmaSet (B.pairs k).x (B.pairs k).y := by
    intro j k hkj
    exact (SetLike.coe_subset_coe.mpr (hHle j)).trans
      (zpowers_subset_sigmaSet' (hgmem j k hkj))
  have hKF : ∀ j k, k ≠ j → f j ⊆ sigmaSet (B.pairs k).x (B.pairs k).y := fun j k hkj =>
    conjugatesOfSet_subset_sigmaSet (hHsub j k hkj)
  -- `f` is injective: if `f j = f j'` for `j ≠ j'`, then `f j ⊆ ⋂ᵢ Σᵢ = {1}`, but `f j`
  -- contains the non-trivial subgroup `H j`.
  have hinj : Set.InjOn f Set.univ := by
    intro j _ j' _ hff
    by_contra hjj
    have hsub1 : ∀ k, f j ⊆ sigmaSet (B.pairs k).x (B.pairs k).y := by
      intro k
      by_cases hk : k = j
      · subst hk
        rw [hff]
        exact hKF j' k hjj
      · exact hKF j k hk
    have hsub : f j ⊆ ⋂ i, sigmaSet (B.pairs i).x (B.pairs i).y :=
      Set.subset_iInter hsub1
    rw [B.inter_sigmaSet_eq_one] at hsub
    have hHj_sub : (↑(H j) : Set G) ⊆ ({1} : Set G) :=
      (Group.subset_conjugatesOfSet).trans hsub
    have hsubsingle : Subsingleton (H j) :=
      ⟨fun a b => Subtype.ext ((hHj_sub a.2).trans (hHj_sub b.2).symm)⟩
    have hcard1 : Nat.card (H j) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsubsingle
    have h2 := (hHmin j).two_le
    omega
  -- For `j ≠ i₀`, `f j ∈ minimalClassesIn Σᵢ₀`, and `f` is injective on `univ.erase i₀`.
  have hmaps : ∀ j ∈ (↑(Finset.univ.erase i₀) : Set B.ι),
      f j ∈ minimalClassesIn (sigmaSet (B.pairs i₀).x (B.pairs i₀).y) := by
    intro j hj
    rw [Finset.mem_coe, Finset.mem_erase] at hj
    exact ⟨H j, hHmin j, rfl, hKF j i₀ (Ne.symm hj.1)⟩
  have hinjon : Set.InjOn f (↑(Finset.univ.erase i₀) : Set B.ι) :=
    hinj.mono (Set.subset_univ _)
  have hle : (↑(Finset.univ.erase i₀) : Set B.ι).ncard
      ≤ kSigma (sigmaSet (B.pairs i₀).x (B.pairs i₀).y) :=
    Set.ncard_le_ncard_of_injOn f hmaps hinjon (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hle
  rw [GeneralisedBeauvilleStructure.dimension, ← Finset.card_univ,
    ← Finset.card_erase_add_one (Finset.mem_univ i₀)]
  omega

/-! ## Section 3, continued: `k(Σ) ≤ 3` for groups of prime-power element order -/

omit [Finite G] in
/-- Conjugation by `c` preserves the order of an element. -/
theorem orderOf_conj (c g : G) : orderOf (c * g * c⁻¹) = orderOf g := by
  have h := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective g
  simpa using h

omit [Finite G] in
/-- Conjugating a subgroup `K` by `c` does not change its set of conjugates. -/
theorem conjugatesOfSet_map_conj (c : G) (K : Subgroup G) :
    Group.conjugatesOfSet (↑(K.map (MulAut.conj c).toMonoidHom) : Set G)
      = Group.conjugatesOfSet (↑K : Set G) := by
  ext b
  simp only [Group.mem_conjugatesOfSet_iff, SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ⟨k, hk, rfl⟩, hac⟩
    have hkc : IsConj k ((MulAut.conj c).toMonoidHom k) := isConj_iff.mpr ⟨c, rfl⟩
    exact ⟨k, hk, hkc.trans hac⟩
  · rintro ⟨k, hk, hac⟩
    have hkc : IsConj k ((MulAut.conj c).toMonoidHom k) := isConj_iff.mpr ⟨c, rfl⟩
    exact ⟨(MulAut.conj c).toMonoidHom k, ⟨k, hk, rfl⟩, hkc.symm.trans hac⟩

/-- The unique minimal (prime-order) subgroup of `⟨g⟩`. Only meaningful when `g ≠ 1`. -/
noncomputable def minimalSubgroup (g : G) : Subgroup G :=
  Subgroup.zpowers (g ^ (orderOf g / (orderOf g).minFac))

/-- For `g ≠ 1`, `minimalSubgroup g` has prime order. -/
theorem isMinimalSubgroup_minimalSubgroup {g : G} (hg : orderOf g ≠ 1) :
    IsMinimalSubgroup (minimalSubgroup g) := by
  have hgpos : orderOf g ≠ 0 := (isOfFinOrder_of_finite g).orderOf_pos.ne'
  unfold IsMinimalSubgroup minimalSubgroup
  rw [Nat.card_zpowers, orderOf_pow_orderOf_div hgpos (Nat.minFac_dvd _)]
  exact Nat.minFac_prime hg

omit [Finite G] in
/-- If `H` is a minimal subgroup and `h ∈ H` is non-identity, then `H = ⟨h⟩`. -/
theorem zpowers_eq_of_isMinimalSubgroup {H : Subgroup G} (hH : IsMinimalSubgroup H) {h : G}
    (hh : h ∈ H) (hh1 : h ≠ 1) : Subgroup.zpowers h = H := by
  haveI : Fact (Nat.card H).Prime := ⟨hH⟩
  have hh1' : (⟨h, hh⟩ : H) ≠ 1 := fun hc => hh1 (congrArg Subtype.val hc)
  have htop : Subgroup.zpowers (⟨h, hh⟩ : H) = ⊤ := zpowers_eq_top_of_prime_card rfl hh1'
  have hmap := congrArg (Subgroup.map H.subtype) htop
  rwa [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap

/-- If `a` has prime order, `⟨a⟩ ≤ ⟨x⟩`, `x ≠ 1`, and `orderOf x` is a prime power, then
`⟨a⟩` is the (unique) minimal subgroup of `⟨x⟩`. -/
theorem zpowers_eq_minimalSubgroup_of_le_zpowers {x a : G} (hx1 : x ≠ 1)
    (hxpp : (orderOf x).primeFactors.card ≤ 1)
    (ha : Subgroup.zpowers a ≤ Subgroup.zpowers x) (haprime : (orderOf a).Prime) :
    Subgroup.zpowers a = minimalSubgroup x := by
  have hxne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  have hxgt1 : 1 < orderOf x := by
    have := (isOfFinOrder_of_finite x).orderOf_pos
    omega
  have hcardpos : 0 < (orderOf x).primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hxgt1)
  have hxpow : IsPrimePow (orderOf x) := by
    rw [isPrimePow_iff_card_primeFactors_eq_one]; omega
  obtain ⟨p, k, hp, hk, hpk⟩ := hxpow
  haveI : Fact p.Prime := ⟨hp.nat_prime⟩
  obtain ⟨n, hn⟩ := (Subgroup.le_zpowers_iff x (Subgroup.zpowers a)).mp ha
  have hnzero : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.zpowers_one_eq_bot] at hn
    have hcard := Nat.card_zpowers a
    rw [hn] at hcard
    simp only [Subgroup.card_bot] at hcard
    exact haprime.one_lt.ne' hcard.symm
  have horder : orderOf a = orderOf (x ^ n) := by
    rw [← Nat.card_zpowers a, ← Nat.card_zpowers (x ^ n), hn]
  rw [orderOf_pow' x hnzero] at horder
  set d := Nat.gcd (orderOf x) n with hd
  have hd_dvd : d ∣ orderOf x := Nat.gcd_dvd_left _ _
  have hdn : d ∣ n := Nat.gcd_dvd_right _ _
  have hdq : d * orderOf a = orderOf x := by
    rw [horder, mul_comm, Nat.div_mul_cancel hd_dvd]
  have hq_dvd_pk : orderOf a ∣ p ^ k := hpk ▸ Dvd.intro_left d hdq
  have hq_dvd_p : orderOf a ∣ p := haprime.dvd_of_dvd_pow hq_dvd_pk
  have hq_eq_p : orderOf a = p :=
    ((Nat.prime_dvd_prime_iff_eq haprime hp.nat_prime).mp hq_dvd_p)
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hpk' : p ^ k' * p = orderOf x := by rw [← hpk, pow_succ]
  have hd_eq : d = p ^ k' := by
    rw [hq_eq_p] at hdq
    exact Nat.eq_of_mul_eq_mul_right hp.nat_prime.pos (hdq.trans hpk'.symm)
  have hdvdn : p ^ k' ∣ n := hd_eq ▸ hdn
  obtain ⟨m, rfl⟩ := hdvdn
  have hxn : x ^ (p ^ k' * m) ∈ Subgroup.zpowers (x ^ p ^ k') := by
    rw [pow_mul]; exact Subgroup.npow_mem_zpowers _ m
  have hle : Subgroup.zpowers a ≤ Subgroup.zpowers (x ^ p ^ k') :=
    hn ▸ Subgroup.zpowers_le_of_mem hxn
  have hminFac : (orderOf x).minFac = p := by
    set q := (orderOf x).minFac with hqdef
    have h1 : q.Prime := Nat.minFac_prime hxne1
    have h2 : q ∣ orderOf x := Nat.minFac_dvd _
    rw [← hpk] at h2
    exact (Nat.prime_dvd_prime_iff_eq h1 hp.nat_prime).mp (h1.dvd_of_dvd_pow h2)
  have hminimal : minimalSubgroup x = Subgroup.zpowers (x ^ p ^ k') := by
    unfold minimalSubgroup
    rw [hminFac, ← hpk', Nat.mul_div_cancel _ hp.nat_prime.pos]
  have hxpos : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
  have hpdvd : p ∣ orderOf x := ⟨p ^ k', by rw [← hpk']; ring⟩
  have hdiv : orderOf x / p = p ^ k' := by
    rw [← hpk', Nat.mul_div_cancel _ hp.nat_prime.pos]
  have hcard_min : Nat.card (minimalSubgroup x) = p := by
    rw [hminimal, Nat.card_zpowers, ← hdiv]
    exact orderOf_pow_orderOf_div hxpos hpdvd
  have hcard_a : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers, hq_eq_p]
  have hle' : Subgroup.zpowers a ≤ minimalSubgroup x := by rw [hminimal]; exact hle
  exact Subgroup.eq_of_le_of_card_ge hle' (le_of_eq (hcard_min.trans hcard_a.symm))

/-- **Theorem 3.6 (special case).** If every element of `G` has prime-power order, every
conjugacy class of minimal subgroups contained in `Σ(x, y)` is the conjugacy class of one of
the minimal subgroups of `⟨x⟩`, `⟨y⟩`, `⟨x*y⟩`. -/
theorem minimalClassesIn_sigmaSet_subset {x y : G}
    (hpp : ∀ g : G, (orderOf g).primeFactors.card ≤ 1) :
    minimalClassesIn (sigmaSet x y) ⊆
      ({Group.conjugatesOfSet (↑(minimalSubgroup x) : Set G),
        Group.conjugatesOfSet (↑(minimalSubgroup y) : Set G),
        Group.conjugatesOfSet (↑(minimalSubgroup (x * y)) : Set G)} : Set (Set G)) := by
  rintro C ⟨H, hHmin, rfl, hHsub⟩
  obtain ⟨h, hhH, hh1⟩ : ∃ h ∈ H, h ≠ 1 := by
    by_contra hc
    push Not at hc
    have hsubsingle : Subsingleton H := ⟨fun a b => Subtype.ext ((hc a a.2).trans (hc b b.2).symm)⟩
    have h1 := Finite.card_le_one_iff_subsingleton.mpr hsubsingle
    have h2 := hHmin.two_le
    omega
  have hzh : Subgroup.zpowers h = H := zpowers_eq_of_isMinimalSubgroup hHmin hhH hh1
  have hhmem : h ∈ sigmaSet x y :=
    hHsub (Group.subset_conjugatesOfSet (hzh ▸ Subgroup.mem_zpowers h))
  obtain ⟨a, ha, hac⟩ := Group.mem_conjugatesOfSet_iff.mp hhmem
  obtain ⟨c, hc⟩ := isConj_iff.mp hac
  have hordah : orderOf a = orderOf h := by rw [← hc]; exact (orderOf_conj c a).symm
  have hordh : orderOf h = Nat.card H := by rw [← hzh, Nat.card_zpowers]
  have haprime : (orderOf a).Prime := by rw [hordah, hordh]; exact hHmin
  have key : ∀ g : G, a ∈ Subgroup.zpowers g → Subgroup.zpowers a = minimalSubgroup g := by
    intro g hag
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hag
      subst hag
      exact haprime.one_lt.ne' orderOf_one
    exact zpowers_eq_minimalSubgroup_of_le_zpowers hg1 (hpp g)
      (Subgroup.zpowers_le.mpr hag) haprime
  have hHeq : H = (Subgroup.zpowers a).map (MulAut.conj c).toMonoidHom := by
    rw [MonoidHom.map_zpowers, ← hzh, ← hc]
    rfl
  rcases ha with (ha | ha) | ha
  · rw [hHeq, key x ha, conjugatesOfSet_map_conj]
    simp
  · rw [hHeq, key y ha, conjugatesOfSet_map_conj]
    simp
  · rw [hHeq, key (x * y) ha, conjugatesOfSet_map_conj]
    simp

/-- **Corollary (special case of Thm 3.6).** If every element of `G` has prime-power order,
then `k(Σ(x, y)) ≤ 3`. -/
theorem kSigma_sigmaSet_le_three {x y : G}
    (hpp : ∀ g : G, (orderOf g).primeFactors.card ≤ 1) :
    kSigma (sigmaSet x y) ≤ 3 := by
  unfold kSigma
  calc (minimalClassesIn (sigmaSet x y)).ncard
      ≤ ({Group.conjugatesOfSet (↑(minimalSubgroup x) : Set G),
          Group.conjugatesOfSet (↑(minimalSubgroup y) : Set G),
          Group.conjugatesOfSet (↑(minimalSubgroup (x * y)) : Set G)} : Set (Set G)).ncard :=
        Set.ncard_le_ncard (minimalClassesIn_sigmaSet_subset hpp) (Set.toFinite _)
    _ ≤ 3 := by
        have h1 := Set.ncard_insert_le (Group.conjugatesOfSet (↑(minimalSubgroup x) : Set G))
          ({Group.conjugatesOfSet (↑(minimalSubgroup y) : Set G),
            Group.conjugatesOfSet (↑(minimalSubgroup (x * y)) : Set G)} : Set (Set G))
        have h2 := Set.ncard_insert_le (Group.conjugatesOfSet (↑(minimalSubgroup y) : Set G))
          ({Group.conjugatesOfSet (↑(minimalSubgroup (x * y)) : Set G)} : Set (Set G))
        rw [Set.ncard_singleton] at h2
        omega

/-- **Corollary 3.10 (headline, special case).** If every element of `G` has prime-power
order, every primitive generalised Beauville structure of `G` has dimension at most `4`. -/
theorem dimension_le_four_of_primePowerOrder (B : GeneralisedBeauvilleStructure G)
    (hB : B.IsPrimitive) (hpp : ∀ g : G, (orderOf g).primeFactors.card ≤ 1) :
    B.dimension ≤ 4 := by
  rcases isEmpty_or_nonempty B.ι with hempty | hne
  · simp [GeneralisedBeauvilleStructure.dimension, Fintype.card_eq_zero]
  · obtain ⟨i₀⟩ := hne
    have h1 := dimension_le_one_add_kSigma B hB i₀
    have h2 := kSigma_sigmaSet_le_three (x := (B.pairs i₀).x) (y := (B.pairs i₀).y) hpp
    omega

/-- **Corollary 3.10 (headline, special case), spectrum form.** If every element of `G` has
prime-power order, every element of `BeauvilleSpectrum G` is at most `4`. -/
theorem maxBSpec_le_four_of_primePowerOrder (hpp : ∀ g : G, (orderOf g).primeFactors.card ≤ 1) :
    ∀ d ∈ BeauvilleSpectrum G, d ≤ 4 := by
  rintro d ⟨B, hBprim, rfl⟩
  exact dimension_le_four_of_primePowerOrder B hBprim hpp
