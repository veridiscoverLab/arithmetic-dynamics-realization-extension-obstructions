import ArithDyn.Derksen.FundRec

/-!
# Galois descent of fundamental recurrences (paper Lemma 2.4)

If `L/K` is a finite Galois extension of fields and `u : ℤ → L` is a fundamental bi-infinite
recurrence, then the norm sequence `n ↦ N_{L/K}(u n)` is a fundamental bi-infinite recurrence
over `K` with the same zero set. Hence `𝓡_L ⊆ 𝓡_K` (`RClass.descent`); in the paper this is
used with `L = 𝔽_{p^s}(t)`, `K = 𝔽_p(t)`.

Proof: `N(u n) = ∏_σ σ(u n)` is a product of conjugate recurrences, hence a recurrence over `L`,
say `w = ℓ Aⁿ v`. Its characteristic polynomial `H` annihilates `w`, hence so does
`H' = ∏_σ σ(H)`, which is Galois-invariant and therefore has coefficients in `K`
(`Polynomial.lifts`), is monic and has nonzero constant term (`± ∏_σ σ(det A)`).
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

open Matrix Finset Polynomial

universe u

variable {K : Type u} [Field K]

/-! ### Closure properties of `IsFundRec` -/

theorem IsFundRec.map {M : Type*} [Field M] {u : ℤ → K} (hu : IsFundRec u) (f : K →+* M) :
    IsFundRec (fun n => f (u n)) := by
  obtain ⟨P, hmonic, hc₀, hrec⟩ := hu
  refine ⟨P.map f, hmonic.map f, ?_, fun n => ?_⟩
  · rw [Polynomial.coeff_map]
    exact (map_ne_zero_iff f f.injective).2 hc₀
  · rw [hmonic.natDegree_map f]
    simp only [Polynomial.coeff_map]
    simp_rw [← map_mul, ← map_sum, hrec n, map_zero]

theorem IsFundRec.mul {u v : ℤ → K} (hu : IsFundRec u) (hv : IsFundRec v) :
    IsFundRec (fun n => u n * v n) := by
  obtain ⟨ι, _, _, r, rfl⟩ := exists_rep_of_isFundRec hu
  obtain ⟨κ, _, _, s, rfl⟩ := exists_rep_of_isFundRec hv
  have := isFundRec_of_rep (r.mul s)
  convert this using 1
  funext n
  rw [LinRepZ.mul_seq]

theorem IsFundRec.const (c : K) : IsFundRec (fun _ : ℤ => c) := by
  refine ⟨Polynomial.X - Polynomial.C 1, Polynomial.monic_X_sub_C 1, by simp, fun n => ?_⟩
  rw [Polynomial.natDegree_X_sub_C, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_X_one,
    Polynomial.coeff_C_zero, Polynomial.coeff_C_ne_zero one_ne_zero]
  ring

theorem IsFundRec.prod {ι : Type*} (s : Finset ι) (u : ι → ℤ → K)
    (h : ∀ i ∈ s, IsFundRec (u i)) : IsFundRec (fun n => ∏ i ∈ s, u i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsFundRec.const (1 : K)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-! ### Polynomials in `A` annihilating `ℓ Aⁿ v` -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- If `P(A) = 0` then `P` annihilates the sequence `ℓ Aⁿ v`. -/
theorem LinRepZ.ann_of_aeval_eq_zero (r : LinRepZ K ι) {P : Polynomial K}
    (hP : Polynomial.aeval r.A P = 0) (n : ℤ) :
    ∑ i ∈ range (P.natDegree + 1), P.coeff i * r.seq (n + i) = 0 := by
  classical
  rw [Polynomial.aeval_eq_sum_range] at hP
  have key : ∀ i : ℕ, P.coeff i * r.seq (n + i) =
      r.ℓ ⬝ᵥ (r.A ^ n *ᵥ ((P.coeff i • r.A ^ i) *ᵥ r.v)) := by
    intro i
    simp only [LinRepZ.seq]
    rw [Matrix.zpow_add r.hA, _root_.zpow_natCast, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  simp only [key]
  rw [← dotProduct_sum, ← Matrix.mulVec_sum, ← Matrix.sum_mulVec, hP]
  simp

lemma LinRepZ.charpoly_coeff_zero_ne_zero (r : LinRepZ K ι) : r.A.charpoly.coeff 0 ≠ 0 := by
  intro h
  have := Matrix.det_eq_sign_charpoly_coeff r.A
  rw [h, mul_zero] at this
  exact r.hA.ne_zero this

/-! ### Descent along a finite Galois extension -/

section Galois

variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Lemma 2.4 (Galois descent).** The norm of a fundamental bi-infinite recurrence over `L` is
a fundamental bi-infinite recurrence over `K`. -/
theorem IsFundRec.norm {u : ℤ → L} (hu : IsFundRec u) :
    IsFundRec (fun n => Algebra.norm K (u n)) := by
  classical
  -- the product of the conjugate sequences is a recurrence over `L` taking values in `K`
  have hwrec : IsFundRec (fun n => ∏ σ : L ≃ₐ[K] L, σ (u n)) :=
    IsFundRec.prod (ι := L ≃ₐ[K] L) Finset.univ (fun σ n => σ (u n))
      (fun (σ : L ≃ₐ[K] L) _ => hu.map (σ : L →+* L))
  have hwv : ∀ n, (∏ σ : L ≃ₐ[K] L, σ (u n)) = algebraMap K L (Algebra.norm K (u n)) :=
    fun n => (Algebra.norm_eq_prod_automorphisms K (u n)).symm
  -- a state representation and the product of the conjugates of its characteristic polynomial
  obtain ⟨ι, _, _, r, hr⟩ := exists_rep_of_isFundRec hwrec
  obtain ⟨H', hH'⟩ : ∃ H' : Polynomial L, H' = ∏ σ : L ≃ₐ[K] L, r.A.charpoly.map (σ : L →+* L) :=
    ⟨_, rfl⟩
  have hH'monic : H'.Monic := by
    rw [hH']
    exact Polynomial.monic_prod_of_monic _ _ (fun σ _ => (Matrix.charpoly_monic _).map _)
  have hH'0 : H'.coeff 0 ≠ 0 := by
    rw [hH', Polynomial.coeff_zero_prod]
    refine Finset.prod_ne_zero_iff.2 (fun σ _ => ?_)
    rw [Polynomial.coeff_map]
    exact (map_ne_zero_iff _ (σ : L →+* L).injective).2 r.charpoly_coeff_zero_ne_zero
  have hH'aeval : Polynomial.aeval r.A H' = 0 := by
    have h1 : r.A.charpoly.map ((1 : L ≃ₐ[K] L) : L →+* L) = r.A.charpoly :=
      Polynomial.ext (fun i => by simp [Polynomial.coeff_map])
    have hsplit : H' = r.A.charpoly *
        ∏ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), r.A.charpoly.map (σ : L →+* L) := by
      rw [hH', ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : L ≃ₐ[K] L)), h1]
    rw [hsplit, map_mul, Matrix.aeval_self_charpoly, zero_mul]
  -- `H'` annihilates the norm sequence
  have hann : ∀ n : ℤ, ∑ i ∈ range (H'.natDegree + 1),
      H'.coeff i * algebraMap K L (Algebra.norm K (u (n + i))) = 0 := by
    intro n
    have := r.ann_of_aeval_eq_zero hH'aeval n
    rw [hr] at this
    simpa only [hwv] using this
  -- `H'` is Galois-invariant, hence defined over `K`
  have hfix : ∀ τ : L ≃ₐ[K] L, H'.map (τ : L →+* L) = H' := by
    intro τ
    rw [hH', Polynomial.map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
    rw [Polynomial.map_map]
    congr 1
    all_goals (ext x; simp [AlgEquiv.mul_apply])
  have hlift : H' ∈ Polynomial.lifts (algebraMap K L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [← IntermediateField.mem_bot, IsGalois.mem_bot_iff_fixed]
    intro τ
    have := congrArg (fun p => Polynomial.coeff p i) (hfix τ)
    simpa [Polynomial.coeff_map] using this
  obtain ⟨Hk, hHk, hdeg, hHkmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hH'monic
  refine ⟨Hk, hHkmonic, ?_, fun n => ?_⟩
  · intro h
    apply hH'0
    rw [← hHk, Polynomial.coeff_map, h, map_zero]
  · apply (algebraMap K L).injective
    rw [map_sum, map_zero, hdeg]
    refine (Finset.sum_congr rfl (fun i _ => ?_)).trans (hann n)
    rw [map_mul, ← hHk, Polynomial.coeff_map]

/-- **Lemma 2.4**: `𝓡_L ⊆ 𝓡_K` for a finite Galois extension `L/K`. -/
theorem RClass.descent {B : Set ℤ} (hB : B ∈ RClass L) : B ∈ RClass K := by
  obtain ⟨u, hu, rfl⟩ := (mem_RClass_iff B).1 hB
  refine (mem_RClass_iff _).2 ⟨fun n => Algebra.norm K (u n), hu.norm, ?_⟩
  ext n
  simp only [Set.mem_setOf_eq]
  exact Algebra.norm_eq_zero_iff

end Galois

/-! ### One-sided recurrences (zero characteristic roots allowed) -/

theorem IsLinRecSeq.map {M : Type*} [Field M] {u : ℕ → K} (hu : IsLinRecSeq u) (f : K →+* M) :
    IsLinRecSeq (fun n => f (u n)) := by
  obtain ⟨E, hE⟩ := exists_isSolution_of_isLinRecSeq hu
  refine isLinRecSeq_of_isSolution ⟨E.order, fun i => f (E.coeffs i)⟩ (fun n => ?_)
  simp only
  rw [hE n, map_sum]
  simp only [map_mul]

theorem IsLinRecSeq.prod {α : Type*} (s : Finset α) (f : α → ℕ → K)
    (h : ∀ i ∈ s, IsLinRecSeq (f i)) : IsLinRecSeq (fun n => ∏ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsLinRecSeq.const (1 : K)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact ((h a (Finset.mem_insert_self a s)).mul
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))).congr (fun n => rfl)

/-- If `P(A) = 0` then `P` annihilates the one-sided sequence `ℓ Aⁿ v`. -/
theorem LinRep.ann_of_aeval_eq_zero (r : LinRep K ι) {P : Polynomial K}
    (hP : Polynomial.aeval r.A P = 0) (n : ℕ) :
    ∑ i ∈ range (P.natDegree + 1), P.coeff i * r.seq (n + i) = 0 := by
  classical
  rw [Polynomial.aeval_eq_sum_range] at hP
  have key : ∀ i : ℕ, P.coeff i * r.seq (n + i) =
      r.ℓ ⬝ᵥ (r.A ^ n *ᵥ ((P.coeff i • r.A ^ i) *ᵥ r.v)) := by
    intro i
    simp only [LinRep.seq]
    rw [pow_add, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul]
  simp only [key]
  rw [← dotProduct_sum, ← Matrix.mulVec_sum, ← Matrix.sum_mulVec, hP]
  simp

section GaloisOneSided

variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Lemma 2.4, one-sided version**: the norm of a linear recurrence sequence over `L` (zero
characteristic roots allowed) is a linear recurrence sequence over `K`. -/
theorem IsLinRecSeq.norm {u : ℕ → L} (hu : IsLinRecSeq u) :
    IsLinRecSeq (fun n => Algebra.norm K (u n)) := by
  classical
  have hwrec : IsLinRecSeq (fun n => ∏ σ : L ≃ₐ[K] L, σ (u n)) :=
    IsLinRecSeq.prod (α := L ≃ₐ[K] L) Finset.univ (fun σ n => σ (u n))
      (fun (σ : L ≃ₐ[K] L) _ => hu.map (σ : L →+* L))
  have hwv : ∀ n, (∏ σ : L ≃ₐ[K] L, σ (u n)) = algebraMap K L (Algebra.norm K (u n)) :=
    fun n => (Algebra.norm_eq_prod_automorphisms K (u n)).symm
  obtain ⟨ι, _, _, r, hr⟩ := hwrec
  obtain ⟨H', hH'⟩ : ∃ H' : Polynomial L, H' = ∏ σ : L ≃ₐ[K] L, r.A.charpoly.map (σ : L →+* L) :=
    ⟨_, rfl⟩
  have hH'monic : H'.Monic := by
    rw [hH']
    exact Polynomial.monic_prod_of_monic _ _ (fun σ _ => (Matrix.charpoly_monic _).map _)
  have hH'aeval : Polynomial.aeval r.A H' = 0 := by
    have h1 : r.A.charpoly.map ((1 : L ≃ₐ[K] L) : L →+* L) = r.A.charpoly :=
      Polynomial.ext (fun i => by simp [Polynomial.coeff_map])
    have hsplit : H' = r.A.charpoly *
        ∏ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), r.A.charpoly.map (σ : L →+* L) := by
      rw [hH', ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : L ≃ₐ[K] L)), h1]
    rw [hsplit, map_mul, Matrix.aeval_self_charpoly, zero_mul]
  have hann : ∀ n : ℕ, ∑ i ∈ range (H'.natDegree + 1),
      H'.coeff i * algebraMap K L (Algebra.norm K (u (n + i))) = 0 := by
    intro n
    have := r.ann_of_aeval_eq_zero hH'aeval n
    rw [hr] at this
    simpa only [hwv] using this
  have hfix : ∀ τ : L ≃ₐ[K] L, H'.map (τ : L →+* L) = H' := by
    intro τ
    rw [hH', Polynomial.map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
    rw [Polynomial.map_map]
    congr 1
    all_goals (ext x; simp [AlgEquiv.mul_apply])
  have hlift : H' ∈ Polynomial.lifts (algebraMap K L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [← IntermediateField.mem_bot, IsGalois.mem_bot_iff_fixed]
    intro τ
    have := congrArg (fun p => Polynomial.coeff p i) (hfix τ)
    simpa [Polynomial.coeff_map] using this
  obtain ⟨Hk, hHk, hdeg, hHkmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hH'monic
  have hrelK : ∀ n : ℕ, ∑ i ∈ range (Hk.natDegree + 1),
      Hk.coeff i * Algebra.norm K (u (n + i)) = 0 := by
    intro n
    apply (algebraMap K L).injective
    rw [map_sum, map_zero, hdeg]
    refine (Finset.sum_congr rfl (fun i _ => ?_)).trans (hann n)
    rw [map_mul, ← hHk, Polynomial.coeff_map]
  refine isLinRecSeq_of_isSolution ⟨Hk.natDegree, fun i => -Hk.coeff i⟩ (fun n => ?_)
  simp only
  have h := hrelK n
  rw [Finset.sum_range_succ, hHkmonic.coeff_natDegree, one_mul, Finset.sum_range] at h
  have hneg : ∑ i : Fin Hk.natDegree, -Hk.coeff (i : ℕ) * Algebra.norm K (u (n + i)) =
      -∑ i : Fin Hk.natDegree, Hk.coeff (i : ℕ) * Algebra.norm K (u (n + i)) := by
    rw [← Finset.sum_neg_distrib]
    simp only [neg_mul]
  rw [hneg]
  linear_combination h

end GaloisOneSided

end ArithDyn.Derksen
