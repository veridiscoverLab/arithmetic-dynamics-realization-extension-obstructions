import ArithDyn.Derksen.Reconstruct
import ArithDyn.Derksen.ValuationPoint
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Auxiliary lemmas for the backward direction of Proposition 2.6

* `exists_compositum`: two field extensions of `κ` embed compatibly into a common field;
* `exists_clear'`: clearing denominators of a polynomial over a fraction field of `F[t]`;
* `exists_generator_orderOf`: a generator of the multiplicative group of a finite field;
* sign-splitting of products of integer powers, and the congruence `∑ dₗ qˡ ≡ ∑ dₗ (mod q - 1)`.
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

open Polynomial

universe u v w

/-- Two field extensions `ι₁ : κ → K₁`, `ι₂ : κ → K₂` embed compatibly into a common field. -/
theorem exists_compositum {κ : Type u} {K₁ : Type v} {K₂ : Type w} [Field κ] [Field K₁] [Field K₂]
    (ι₁ : κ →+* K₁) (ι₂ : κ →+* K₂) :
    ∃ (Ω : Type (max v w)) (_ : Field Ω) (j₁ : K₁ →+* Ω) (j₂ : K₂ →+* Ω),
      j₁.comp ι₁ = j₂.comp ι₂ := by
  letI : Algebra κ K₁ := ι₁.toAlgebra
  letI : Algebra κ K₂ := ι₂.toAlgebra
  haveI : Nontrivial (TensorProduct κ K₁ K₂) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain κ K₁ K₂
      ι₁.injective ι₂.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct κ K₁ K₂)
  letI : Field (TensorProduct κ K₁ K₂ ⧸ m) := Ideal.Quotient.field m
  refine ⟨TensorProduct κ K₁ K₂ ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom (R := κ) (A := K₁) (B := K₂)),
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := κ) (A := K₁) (B := K₂)).toRingHom,
    ?_⟩
  ext x
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  congr 1
  have hx1 : ι₁ x = x • (1 : K₁) := by rw [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
  have hx2 : ι₂ x = x • (1 : K₂) := by rw [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply,
    hx1, hx2, TensorProduct.smul_tmul]

/-- Clearing denominators: every polynomial over a fraction field `K` of `F[t]` is a nonzero
constant multiple of the image of a polynomial over `F[t]`. -/
theorem exists_clear' {F : Type*} [Field F] {K : Type*} [Field K] [Algebra (Polynomial F) K]
    [IsFractionRing (Polynomial F) K] (h : Polynomial K) :
    ∃ (N : Polynomial (Polynomial F)) (b : Polynomial F), b ≠ 0 ∧
      N.map (algebraMap (Polynomial F) K) = C (algebraMap (Polynomial F) K b) * h := by
  obtain ⟨b, hb, hN⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial F)) h
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors (Polynomial F)) h, b,
    nonZeroDivisors.ne_zero hb, ?_⟩
  rw [hN, Algebra.smul_def, Polynomial.algebraMap_apply]

/-- A generator of the multiplicative group of a finite field. -/
theorem exists_generator_orderOf (F : Type*) [Field F] [Fintype F] :
    ∃ ζ : F, ζ ≠ 0 ∧ orderOf ζ = Fintype.card F - 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨(g : F), g.ne_zero, ?_⟩
  rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
    Fintype.card_units]

/-- `∏ᵢ xᵢ^{cᵢ} = (∏_{cᵢ>0} xᵢ^{cᵢ⁺}) / (∏_{cᵢ<0} xᵢ^{cᵢ⁻})` in a field. -/
theorem prod_zpow_eq_div {G : Type*} [Field G] {ι : Type*} (s : Finset ι) (x : ι → G) (c : ι → ℤ) :
    ∏ i ∈ s, x i ^ c i =
      (∏ i ∈ s.filter (fun i => 0 < c i), x i ^ (c i).toNat) /
        ∏ i ∈ s.filter (fun i => c i < 0), x i ^ (-(c i)).toNat := by
  classical
  have hpt : ∀ i, x i ^ c i = x i ^ (c i).toNat / x i ^ (-(c i)).toNat := by
    intro i
    rcases le_or_gt 0 (c i) with h | h
    · have h1 : (-(c i)).toNat = 0 := by omega
      rw [h1, pow_zero, div_one, ← zpow_natCast, Int.toNat_of_nonneg h]
    · have h1 : (c i).toNat = 0 := by omega
      rw [h1, pow_zero, ← zpow_natCast, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -(c i)),
        zpow_neg, one_div, inv_inv]
  simp_rw [hpt]
  rw [Finset.prod_div_distrib, Finset.prod_filter, Finset.prod_filter]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    split_ifs with h
    · rfl
    · have : (c i).toNat = 0 := by omega
      rw [this, pow_zero]
  · apply Finset.prod_congr rfl
    intro i _
    split_ifs with h
    · rfl
    · have : (-(c i)).toNat = 0 := by omega
      rw [this, pow_zero]

/-- `∑ₗ dₗ qˡ ≡ ∑ₗ dₗ (mod q - 1)`. -/
theorem sum_mul_pow_modEq {ι : Type*} (s : Finset ι) (d : ι → ℤ) (ℓ : ι → ℕ) (q : ℤ) :
    ∑ i ∈ s, d i * q ^ ℓ i ≡ ∑ i ∈ s, d i [ZMOD (q - 1)] := by
  apply Int.ModEq.sum
  intro i _
  have h1 : q ≡ 1 [ZMOD (q - 1)] := by
    rw [Int.modEq_iff_dvd]; exact ⟨-1, by ring⟩
  have h2 : q ^ ℓ i ≡ 1 [ZMOD (q - 1)] := by
    simpa using h1.pow (ℓ i)
  simpa using h2.mul_left (d i)

/-- A multiple of `m` of absolute value `< m` is zero. -/
theorem eq_zero_of_dvd_of_natAbs_lt {m : ℕ} {x : ℤ} (hdvd : (m : ℤ) ∣ x) (hlt : x.natAbs < m) :
    x = 0 := by
  rcases eq_or_ne x 0 with h | h
  · exact h
  · exfalso
    have := Int.natAbs_le_of_dvd_ne_zero hdvd h
    omega

end ArithDyn.Derksen
