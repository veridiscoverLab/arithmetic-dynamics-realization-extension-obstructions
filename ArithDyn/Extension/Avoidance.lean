import Mathlib

/-!
# Prime avoidance and height induction (paper §3, auxiliaries for Theorem 3.1)

Pure commutative algebra used in the base-point-freeness argument of Theorem 3.1, which is done
by prime avoidance and Krull dimension instead of a dimension count.

* `exists_notMem_iUnion_of_ne_top` (A): a vector space over an infinite field is not a finite
  union of proper subspaces.
* `exists_mem_coset_notMem` (B): coset prime avoidance over an infinite field.
* `isHomogeneous_of_mem_minimalPrimes` (C): minimal primes of a homogeneous ideal are homogeneous.
* `le_ker_constantCoeff_of_isHomogeneous` (D): a proper homogeneous ideal lies in the irrelevant
  ideal `ker constantCoeff`.
* `eq_ker_constantCoeff_of_primeHeight` (E): a homogeneous prime of height `n` in `κ[X₁,…,Xₙ]` is
  the irrelevant ideal.
* `exists_add_mem_radical` (F): height induction — perturbing `n` homogeneous forms `F₀ i` inside
  a subspace `V ⊆ J` (with `V` contained in no homogeneous prime not containing `J`) produces
  `F i ∈ F₀ i + V` with `J ≤ √(F₁, …, Fₙ)`.
-/

set_option autoImplicit false

namespace ArithDyn.Extension

open MvPolynomial

/-! ### Linear algebra over an infinite field -/

/-- (A) A vector space over an infinite field is not a finite union of proper subspaces. -/
theorem exists_notMem_iUnion_of_ne_top {κ V : Type*} [Field κ] [Infinite κ] [AddCommGroup V]
    [Module κ V] {ι : Type*} (s : Finset ι) (W : ι → Submodule κ V) (hW : ∀ i ∈ s, W i ≠ ⊤) :
    ∃ v : V, ∀ i ∈ s, v ∉ W i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨v, hv⟩ := ih fun i hi => hW i (Finset.mem_insert_of_mem hi)
    by_cases hva : v ∈ W a
    · -- `v` avoids all `W i`, `i ∈ s`, but lies in `W a`: move along the line `u + c • v`.
      obtain ⟨u, hu⟩ : ∃ u, u ∉ W a := by
        by_contra hcon
        exact hW a (Finset.mem_insert_self _ _)
          (eq_top_iff.2 fun x _ => by_contra fun hx => hcon ⟨x, hx⟩)
      -- each `W i` (`i ∈ s`) contains at most one point of the line
      have key : ∀ i ∈ s, ∀ c c' : κ, u + c • v ∈ W i → u + c' • v ∈ W i → c = c' := by
        intro i hi c c' h1 h2
        by_contra hne
        apply hv i hi
        have h3 : (c - c') • v ∈ W i := by
          have := (W i).sub_mem h1 h2
          rwa [add_sub_add_left_eq_sub, ← sub_smul] at this
        have := (W i).smul_mem (c - c')⁻¹ h3
        rwa [inv_smul_smul₀ (sub_ne_zero.2 hne)] at this
      have hfin : (⋃ i ∈ (s : Set ι), {c : κ | u + c • v ∈ W i}).Finite := by
        refine Set.Finite.biUnion s.finite_toSet fun i hi => ?_
        refine Set.Subsingleton.finite ?_
        intro c hc c' hc'
        exact key i hi c c' hc hc'
      obtain ⟨c, hc⟩ := hfin.infinite_compl.nonempty
      refine ⟨u + c • v, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · intro hmem
        apply hu
        have := (W _).sub_mem hmem ((W _).smul_mem c hva)
        rwa [add_sub_cancel_right] at this
      · intro hmem
        exact Set.notMem_of_mem_compl hc (Set.mem_biUnion hi hmem)
    · exact ⟨v, fun i hi => by
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hva
        · exact hv i hi⟩

/-- (B) Coset prime avoidance over an infinite field: if for every ideal `P` in the finite family
it is not the case that `F ∈ P` and `V ⊆ P`, then some element of the coset `F + V` lies in none
of them. -/
theorem exists_mem_coset_notMem {κ S : Type*} [Field κ] [Infinite κ] [CommRing S] [Algebra κ S]
    (V : Submodule κ S) (F : S) {ι : Type*} (s : Finset ι) (P : ι → Ideal S)
    (h : ∀ i ∈ s, ¬ (F ∈ P i ∧ ∀ v ∈ V, v ∈ P i)) :
    ∃ v ∈ V, ∀ i ∈ s, F + v ∉ P i := by
  classical
  -- the linear map `(a, v) ↦ a • F + v` on `κ × V`
  obtain ⟨L, hL⟩ : ∃ L : (κ × V) →ₗ[κ] S, ∀ (a : κ) (v : V), L (a, v) = a • F + (v : S) :=
    ⟨(LinearMap.fst κ κ V).smulRight F + V.subtype ∘ₗ LinearMap.snd κ κ V, fun a v => by simp⟩
  obtain ⟨W, hW⟩ : ∃ W : ι → Submodule κ (κ × V),
      ∀ (i : ι) (a : κ) (v : V), (a, v) ∈ W i ↔ a • F + (v : S) ∈ P i :=
    ⟨fun i => ((P i).restrictScalars κ).comap L, fun i a v => by simp [hL]⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Submodule κ (κ × V), ∀ (a : κ) (v : V), (a, v) ∈ W₀ ↔ a = 0 :=
    ⟨LinearMap.ker (LinearMap.fst κ κ V), fun a v => by simp⟩
  have hW₀top : W₀ ≠ ⊤ := fun htop => by
    have : ((1 : κ), (0 : V)) ∈ W₀ := by rw [htop]; exact Submodule.mem_top
    exact one_ne_zero ((hW₀ 1 0).1 this)
  have hWtop : ∀ i ∈ s, W i ≠ ⊤ := by
    intro i hi htop
    refine h i hi ⟨?_, fun v hv => ?_⟩
    · have : ((1 : κ), (0 : V)) ∈ W i := by rw [htop]; exact Submodule.mem_top
      simpa using (hW i 1 0).1 this
    · have : ((0 : κ), (⟨v, hv⟩ : V)) ∈ W i := by rw [htop]; exact Submodule.mem_top
      simpa using (hW i 0 ⟨v, hv⟩).1 this
  obtain ⟨p, hp⟩ := exists_notMem_iUnion_of_ne_top (insert W₀ (s.image W)) id (by
    intro U hU
    rcases Finset.mem_insert.1 hU with rfl | hU
    · exact hW₀top
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hU
      exact hWtop i hi)
  obtain ⟨a, v⟩ := p
  have ha : a ≠ 0 := fun ha => hp W₀ (Finset.mem_insert_self _ _) ((hW₀ a v).2 ha)
  refine ⟨a⁻¹ • (v : S), V.smul_mem _ v.2, fun i hi hmem => ?_⟩
  refine hp (W i) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem W hi)) ((hW i a v).2 ?_)
  have : a • F + (v : S) = a • (F + a⁻¹ • (v : S)) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ ha, one_smul]
  rw [this]
  exact Submodule.smul_of_tower_mem (P i) a hmem

/-! ### Homogeneous ideals in `κ[X₁, …, Xₙ]` -/

section Graded

variable {κ : Type*} [Field κ] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard grading on `MvPolynomial (Fin n) κ`. -/
local notation "𝒜" => homogeneousSubmodule (Fin n) κ

/-- (C) Minimal primes of a homogeneous ideal are homogeneous. -/
theorem isHomogeneous_of_mem_minimalPrimes {I P : Ideal (MvPolynomial (Fin n) κ)}
    (hI : I.IsHomogeneous 𝒜) (hP : P ∈ I.minimalPrimes) : P.IsHomogeneous 𝒜 := by
  have hPprime : P.IsPrime := hP.1.1
  have hIP : I ≤ P := hP.1.2
  have hcore : (P.homogeneousCore 𝒜).toIdeal.IsPrime := hPprime.homogeneousCore
  have hI_le : I ≤ (P.homogeneousCore 𝒜).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono 𝒜 hIP)
  have hle : (P.homogeneousCore 𝒜).toIdeal ≤ P := Ideal.toIdeal_homogeneousCore_le 𝒜 P
  have heq : (P.homogeneousCore 𝒜).toIdeal = P := le_antisymm hle (hP.2 ⟨hcore, hI_le⟩ hle)
  rw [← heq]
  exact (P.homogeneousCore 𝒜).isHomogeneous

/-- (D) A proper homogeneous ideal is contained in the irrelevant ideal (polynomials with zero
constant term). -/
theorem le_ker_constantCoeff_of_isHomogeneous {I : Ideal (MvPolynomial (Fin n) κ)}
    (hI : I.IsHomogeneous 𝒜) (hne : I ≠ ⊤) :
    I ≤ RingHom.ker (constantCoeff (σ := Fin n) (R := κ)) := by
  intro x hx
  rw [RingHom.mem_ker]
  by_contra hc
  apply hne
  have h0 : (DirectSum.decompose 𝒜 x 0 : MvPolynomial (Fin n) κ) ∈ I := hI 0 hx
  have h0' : (DirectSum.decompose 𝒜 x 0 : MvPolynomial (Fin n) κ) = C (constantCoeff x) :=
    (decomposition.decompose'_apply x 0).trans (homogeneousComponent_zero x)
  rw [h0'] at h0
  exact Ideal.eq_top_of_isUnit_mem I h0 ((isUnit_iff_ne_zero.2 hc).map C)

/-- (E) A homogeneous prime of height `n = dim κ[X_1..X_n]` is the irrelevant ideal. -/
theorem eq_ker_constantCoeff_of_primeHeight {P : Ideal (MvPolynomial (Fin n) κ)} [P.IsPrime]
    (hP : P.IsHomogeneous 𝒜) (hht : (n : ℕ∞) ≤ P.primeHeight) :
    P = RingHom.ker (constantCoeff (σ := Fin n) (R := κ)) := by
  have hdim : ringKrullDim (MvPolynomial (Fin n) κ) = (n : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  haveI : FiniteRingKrullDim (MvPolynomial (Fin n) κ) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, hdim]
    exact ⟨WithBot.natCast_ne_bot n, by
      rw [← WithBot.coe_natCast, ← WithBot.coe_top, Ne, WithBot.coe_inj]
      exact ENat.coe_ne_top n⟩
  have heq : (P.primeHeight : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) κ) := by
    refine le_antisymm Ideal.primeHeight_le_ringKrullDim ?_
    rw [hdim]
    exact_mod_cast hht
  have hmax : P.IsMaximal := Ideal.isMaximal_of_primeHeight_eq_ringKrullDim heq
  exact hmax.eq_of_le (RingHom.ker_ne_top _)
    (le_ker_constantCoeff_of_isHomogeneous hP hmax.ne_top)

set_option maxHeartbeats 800000 in
/-- (F) **Height induction.** Let `J` be a proper homogeneous ideal, `V ⊆ J` a `κ`-subspace of
forms of degree `d` such that no homogeneous prime `P` with `J ⊄ P` contains `V`. Then for any
`n` forms `F₀ i` of degree `d` there are `F i ∈ F₀ i + V` such that every prime containing all
`F i` contains `J` (equivalently `J ≤ (span (range F)).radical`). -/
theorem exists_add_mem_radical [Infinite κ] (J : Ideal (MvPolynomial (Fin n) κ))
    (hJ : J.IsHomogeneous 𝒜) (hJne : J ≠ ⊤) (V : Submodule κ (MvPolynomial (Fin n) κ))
    (hVJ : ∀ v ∈ V, v ∈ J)
    (hV : ∀ P : Ideal (MvPolynomial (Fin n) κ), P.IsPrime → P.IsHomogeneous 𝒜 → ¬ J ≤ P →
      ¬ (∀ v ∈ V, v ∈ P))
    (F₀ : Fin n → MvPolynomial (Fin n) κ) (d : ℕ) (hF₀ : ∀ i, (F₀ i).IsHomogeneous d)
    (hVd : ∀ v ∈ V, v.IsHomogeneous d) :
    ∃ F : Fin n → MvPolynomial (Fin n) κ, (∀ i, F i - F₀ i ∈ V) ∧
      J ≤ (Ideal.span (Set.range F)).radical := by
  classical
  -- every perturbation `F i ∈ F₀ i + V` is again a form of degree `d`
  have hhom : ∀ F : Fin n → MvPolynomial (Fin n) κ, (∀ i, F i - F₀ i ∈ V) →
      ∀ i, SetLike.IsHomogeneousElem 𝒜 (F i) := by
    intro F hFV i
    refine ⟨d, ?_⟩
    have : F i = F₀ i + (F i - F₀ i) := by ring
    rw [this]
    exact (𝒜 d).add_mem ((mem_homogeneousSubmodule _ _).2 (hF₀ i))
      ((mem_homogeneousSubmodule _ _).2 (hVd _ (hFV i)))
  -- main induction: after choosing the `F i`, `i ∈ s`, every minimal prime of `(F i)_{i ∈ s}`
  -- not containing `J` has height at least `|s|`.
  have hmain : ∀ s : Finset (Fin n), ∃ F : Fin n → MvPolynomial (Fin n) κ,
      (∀ i, F i - F₀ i ∈ V) ∧
      ∀ P ∈ (Ideal.span (F '' (s : Set (Fin n)))).minimalPrimes, ¬ J ≤ P →
        (s.card : ℕ∞) ≤ P.height := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨F₀, fun i => by simp, ?_⟩
      intro P _ _
      simp
    | insert a s ha ih =>
      obtain ⟨F, hFV, hF⟩ := ih
      have hspan : (Ideal.span (F '' (s : Set (Fin n)))).IsHomogeneous 𝒜 :=
        Ideal.homogeneous_span 𝒜 _ (by rintro _ ⟨i, -, rfl⟩; exact hhom F hFV i)
      -- the finite set of minimal primes of `(F i)_{i ∈ s}` not containing `J`
      obtain ⟨Ps, hPs⟩ : ∃ Ps : Finset (Ideal (MvPolynomial (Fin n) κ)),
          ∀ P, P ∈ Ps ↔ P ∈ (Ideal.span (F '' (s : Set (Fin n)))).minimalPrimes ∧ ¬ J ≤ P := by
        have hfin : ((Ideal.span (F '' (s : Set (Fin n)))).minimalPrimes ∩
            {P | ¬ J ≤ P}).Finite :=
          (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset Set.inter_subset_left
        exact ⟨hfin.toFinset, fun P => by simp⟩
      -- prime avoidance: choose `F a ∈ F₀ a + V` outside all of them
      obtain ⟨v, hvV, hv⟩ := exists_mem_coset_notMem V (F₀ a) Ps id (by
        intro P hP
        obtain ⟨hPmin, hJP⟩ := (hPs P).1 hP
        have hPprime : P.IsPrime := Ideal.minimalPrimes_isPrime hPmin
        have hPhom : P.IsHomogeneous 𝒜 := isHomogeneous_of_mem_minimalPrimes hspan hPmin
        exact fun h' => hV P hPprime hPhom hJP h'.2)
      refine ⟨Function.update F a (F₀ a + v), ?_, ?_⟩
      · intro i
        by_cases hia : i = a
        · subst hia; simp [hvV]
        · rw [Function.update_of_ne hia]; exact hFV i
      · intro Q hQ hJQ
        have himg : Function.update F a (F₀ a + v) '' ((insert a s : Finset (Fin n)) : Set (Fin n))
            = insert (F₀ a + v) (F '' (s : Set (Fin n))) := by
          have hrest : Function.update F a (F₀ a + v) '' (s : Set (Fin n)) =
              F '' (s : Set (Fin n)) := by
            apply Set.image_congr
            intro i hi
            apply Function.update_of_ne
            rintro rfl
            exact ha hi
          rw [Finset.coe_insert, Set.image_insert_eq, Function.update_self, hrest]
        rw [himg] at hQ
        have hQprime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
        have hle : Ideal.span (F '' (s : Set (Fin n))) ≤ Q :=
          (Ideal.span_mono (Set.subset_insert _ _)).trans hQ.1.2
        obtain ⟨P, hPmin, hPQ⟩ := Ideal.exists_minimalPrimes_le hle
        have hJP : ¬ J ≤ P := fun h' => hJQ (h'.trans hPQ)
        have hPprime : P.IsPrime := Ideal.minimalPrimes_isPrime hPmin
        have hnot : F₀ a + v ∉ P := hv P ((hPs P).2 ⟨hPmin, hJP⟩)
        have hmem : F₀ a + v ∈ Q := hQ.1.2 (Ideal.subset_span (Set.mem_insert _ _))
        have hlt : P < Q := lt_of_le_of_ne hPQ (by rintro rfl; exact hnot hmem)
        have h1 := Ideal.primeHeight_add_one_le_of_lt hlt
        have h2 := hF P hPmin hJP
        rw [Ideal.height_eq_primeHeight] at h2 ⊢
        rw [Finset.card_insert_of_notMem ha, Nat.cast_succ]
        exact (add_le_add h2 (le_refl (1 : ℕ∞))).trans h1
  obtain ⟨F, hFV, hF⟩ := hmain Finset.univ
  refine ⟨F, hFV, ?_⟩
  rw [← Ideal.sInf_minimalPrimes]
  refine le_sInf fun Q hQ => ?_
  by_contra hJQ
  have hQprime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
  have hspan : (Ideal.span (Set.range F)).IsHomogeneous 𝒜 :=
    Ideal.homogeneous_span 𝒜 _ (by rintro _ ⟨i, rfl⟩; exact hhom F hFV i)
  have hQhom : Q.IsHomogeneous 𝒜 := isHomogeneous_of_mem_minimalPrimes hspan hQ
  have hht : (n : ℕ∞) ≤ Q.primeHeight := by
    rw [Finset.coe_univ, Set.image_univ] at hF
    have := hF Q hQ hJQ
    rw [Ideal.height_eq_primeHeight] at this
    simpa using this
  have hQeq : Q = RingHom.ker (constantCoeff (σ := Fin n) (R := κ)) :=
    eq_ker_constantCoeff_of_primeHeight hQhom hht
  exact hJQ (by rw [hQeq]; exact le_ker_constantCoeff_of_isHomogeneous hJ hJne)

end Graded

end ArithDyn.Extension
