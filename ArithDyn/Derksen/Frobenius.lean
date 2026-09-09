import Mathlib

/-!
# Toolkit for the Frobenius reconstruction lemma (paper Lemma 2.5)

We work in `B = F[t][X] = Polynomial (Polynomial F)`: the outer variable is `X`, the inner
variable is `t`. This file provides
* the coefficientwise derivation `dt = ∂/∂t` on `B` (a genuine `Derivation`, via
  `Differential.mapCoeffs`), its interaction with evaluation `X ↦ a` and with `X`-degrees;
* the coefficientwise Frobenius `Φ` (`t ↦ t^p` on coefficients, `X` fixed), its interaction with
  evaluation, and the fact that `dt N = 0` forces `N = Φ N'` (perfect coefficient field);
* Eisenstein: `X^{p^k} + t` is irreducible (hence prime) in `B`;
* the "logarithmic derivative" lemma: if `dt N * D = N * dt D` with `N, D` coprime in `B`,
  then `dt N = 0` and `dt D = 0`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ArithDyn.Derksen

open Polynomial

variable {F : Type*} [Field F]

/-- The differential structure `d/dt` on `F[t]`. -/
noncomputable instance instDifferentialPolynomial : Differential (Polynomial F) where
  deriv :=
    { toLinearMap := (Polynomial.derivative : Polynomial F →ₗ[F] Polynomial F).restrictScalars ℤ
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        simp only [LinearMap.restrictScalars_apply, Polynomial.derivative_mul, smul_eq_mul]
        ring }

lemma deriv_eq (a : Polynomial F) : (Differential.deriv a : Polynomial F) = Polynomial.derivative a := rfl

/-- `∂/∂t` on `F[t][X]`, coefficientwise. -/
noncomputable def dt : Derivation ℤ (Polynomial (Polynomial F)) (Polynomial (Polynomial F)) :=
  Differential.mapCoeffs

@[simp] lemma coeff_dt (N : Polynomial (Polynomial F)) (i : ℕ) :
    (dt N).coeff i = Polynomial.derivative (N.coeff i) := rfl

@[simp] lemma dt_C (a : Polynomial F) : dt (C a) = C (Polynomial.derivative a) := by
  ext i; simp [coeff_C]; split_ifs <;> simp

@[simp] lemma dt_X : dt (X : Polynomial (Polynomial F)) = 0 := by
  ext i; simp [coeff_X]; split_ifs <;> simp

lemma dt_mul (N M : Polynomial (Polynomial F)) : dt (N * M) = dt N * M + N * dt M := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring

lemma dt_pow (N : Polynomial (Polynomial F)) (n : ℕ) :
    dt (N ^ n) = n * N ^ (n - 1) * dt N := by
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]; ring

lemma natDegree_dt_le (N : Polynomial (Polynomial F)) : (dt N).natDegree ≤ N.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.2
  intro i hi
  rw [coeff_dt, Polynomial.coeff_eq_zero_of_natDegree_lt hi, Polynomial.derivative_zero]

/-- `∂/∂t` commutes with evaluation at a constant `a ∈ F` (as `X ↦ C a`). -/
lemma derivative_eval_C (a : F) (N : Polynomial (Polynomial F)) :
    Polynomial.derivative (N.eval (C a)) = (dt N).eval (C a) := by
  induction N using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    simp only [eval_monomial, Polynomial.derivative_mul, Polynomial.derivative_pow]
    have h1 : dt (monomial n c) = monomial n (Polynomial.derivative c) := by
      ext i; simp [coeff_monomial]; split_ifs <;> simp
    rw [h1, eval_monomial]
    simp [Polynomial.derivative_C]

/-! ### Coefficientwise Frobenius -/

variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- `Φ : F[t][X] → F[t][X]`, `t ↦ t^p` on coefficients (the `p`-th power on `F[t]`), `X` fixed. -/
noncomputable def Φ : Polynomial (Polynomial F) →+* Polynomial (Polynomial F) :=
  Polynomial.mapRingHom (frobenius (Polynomial F) p)

lemma Φ_apply (N : Polynomial (Polynomial F)) : Φ p N = N.map (frobenius (Polynomial F) p) := rfl

@[simp] lemma Φ_C (a : Polynomial F) : Φ p (C a) = C (a ^ p) := by
  simp [Φ_apply, frobenius_def]

@[simp] lemma Φ_X : Φ p (X : Polynomial (Polynomial F)) = X := by simp [Φ_apply]

lemma Φ_injective : Function.Injective (Φ (F := F) p) :=
  Polynomial.map_injective _ (frobenius_inj (Polynomial F) p)

lemma natDegree_Φ (N : Polynomial (Polynomial F)) : (Φ p N).natDegree = N.natDegree :=
  Polynomial.natDegree_map_eq_of_injective (frobenius_inj (Polynomial F) p) N

/-- Frobenius and evaluation: `(Φ N)(a^p) = (N(a))^p`. -/
lemma eval_Φ (a : F) (N : Polynomial (Polynomial F)) :
    (Φ p N).eval (C (a ^ p)) = (N.eval (C a)) ^ p := by
  rw [Φ_apply, eval_map]
  have : (C (a ^ p) : Polynomial F) = frobenius (Polynomial F) p (C a) := by
    rw [frobenius_def, map_pow]
  rw [this, Polynomial.eval₂_at_apply, frobenius_def]

/-- If all `t`-derivatives of the coefficients vanish, `N` is in the image of `Φ`
(perfect coefficient field). -/
lemma exists_Φ_eq [PerfectRing F p] (N : Polynomial (Polynomial F)) (h : dt N = 0) :
    ∃ N' : Polynomial (Polynomial F), Φ p N' = N := by
  classical
  -- coefficientwise: `c = expand p (contract p c) = (map frob⁻¹ (contract p c)) ^ p`
  have key : ∀ c : Polynomial F, Polynomial.derivative c = 0 →
      ∃ g : Polynomial F, frobenius (Polynomial F) p g = c := by
    intro c hc
    refine ⟨(Polynomial.contract p c).map (frobeniusEquiv F p).symm, ?_⟩
    rw [frobenius_def, ← Polynomial.map_frobenius_expand, Polynomial.map_expand, Polynomial.map_map]
    have : (frobenius F p).comp ((frobeniusEquiv F p).symm : F →+* F) = RingHom.id F := by
      ext x
      simp
    rw [this, Polynomial.map_id, Polynomial.expand_contract p hc (Fact.out : p.Prime).ne_zero]
  choose g hg using key
  refine ⟨∑ i ∈ N.support, C (g (N.coeff i) (by
      have := congrArg (fun q => Polynomial.coeff q i) h
      simpa using this)) * X ^ i, ?_⟩
  rw [map_sum]
  conv_rhs => rw [N.as_sum_support_C_mul_X_pow]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, Φ_X, Φ_C, ← frobenius_def, hg]

/-! ### Eisenstein: `X^{p^k} + t` is prime in `F[t][X]` -/

/-- The polynomial `f_k = X^{p^k} + t`. -/
noncomputable def fk (k : ℕ) : Polynomial (Polynomial F) := X ^ (p ^ k) + C Polynomial.X

lemma fk_monic (k : ℕ) : (fk (F := F) p k).Monic := by
  unfold fk
  apply Polynomial.Monic.add_of_left (Polynomial.monic_X_pow _)
  rw [Polynomial.degree_X_pow]
  exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast pow_pos (Fact.out : p.Prime).pos k)

lemma fk_natDegree (k : ℕ) : (fk (F := F) p k).natDegree = p ^ k := by
  unfold fk
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;>
    simp [Polynomial.natDegree_X_pow, pow_pos (Fact.out : p.Prime).pos k]

lemma fk_ne_zero (k : ℕ) : (fk (F := F) p k) ≠ 0 := (fk_monic p k).ne_zero

lemma fk_degree (k : ℕ) : (fk (F := F) p k).degree = (p ^ k : ℕ) := by
  rw [Polynomial.degree_eq_natDegree (fk_ne_zero p k), fk_natDegree]

lemma coeff_fk (k m : ℕ) : (fk (F := F) p k).coeff m =
    (if m = p ^ k then 1 else 0) + (if m = 0 then Polynomial.X else 0) := by
  simp only [fk, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]

@[simp] lemma dt_fk (k : ℕ) : dt (fk (F := F) p k) = 1 := by
  unfold fk
  rw [map_add, dt_pow, dt_X, dt_C, Polynomial.derivative_X, mul_zero, zero_add, map_one]

lemma eval_C_fk (k : ℕ) (a : F) :
    (fk (F := F) p k).eval (C a) = Polynomial.X + C (a ^ p ^ k) := by
  simp [fk, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, add_comm]

lemma Φ_fk (k : ℕ) : Φ p (fk (F := F) p k) = X ^ (p ^ k) + C (Polynomial.X ^ p) := by
  simp [fk, Φ_apply, frobenius_def]

/-- Eisenstein at the prime `t` of `F[t]`: `X^{p^k} + t` is irreducible in `F[t][X]`. -/
lemma fk_irreducible (k : ℕ) : Irreducible (fk (F := F) p k) := by
  have hP : (Ideal.span {(Polynomial.X : Polynomial F)}).IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X
  apply Polynomial.irreducible_of_eisenstein_criterion hP
  · rw [(fk_monic p k).leadingCoeff, Ideal.mem_span_singleton]
    intro h
    have := Polynomial.X_dvd_iff.1 h
    simp at this
  · intro m hm
    rw [fk_degree] at hm
    have hm' : m < p ^ k := by exact_mod_cast hm
    rw [coeff_fk, if_neg hm'.ne, zero_add]
    split_ifs
    · exact Ideal.mem_span_singleton_self _
    · exact Ideal.zero_mem _
  · rw [fk_degree]; exact_mod_cast pow_pos (Fact.out : p.Prime).pos k
  · rw [coeff_fk, if_neg (pow_pos (Fact.out : p.Prime).pos k).ne, if_pos rfl, zero_add,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have := Polynomial.natDegree_le_of_dvd h Polynomial.X_ne_zero
    simp at this
  · exact (fk_monic p k).isPrimitive

lemma fk_prime (k : ℕ) : Prime (fk (F := F) p k) := (fk_irreducible p k).prime

/-! ### Units, coprimality and `Φ` -/

lemma isUnit_iff_B (N : Polynomial (Polynomial F)) :
    IsUnit N ↔ ∃ c : F, c ≠ 0 ∧ N = C (C c) := by
  constructor
  · intro h
    obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.1 h
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.1 hr
    exact ⟨c, hc.ne_zero, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact Polynomial.isUnit_C.2 (Polynomial.isUnit_C.2 hc.isUnit)

lemma isRelPrime_of_Φ [PerfectRing F p] {N D : Polynomial (Polynomial F)}
    (h : IsRelPrime (Φ p N) (Φ p D)) : IsRelPrime N D := by
  intro d hdN hdD
  have hu : IsUnit (Φ p d) := h (_root_.map_dvd _ hdN) (_root_.map_dvd _ hdD)
  obtain ⟨c, hc, hcd⟩ := (isUnit_iff_B _).1 hu
  obtain ⟨c', hc'⟩ := (frobeniusEquiv F p).surjective c
  have : Φ p (C (C c')) = Φ p d := by
    rw [Φ_C, ← Polynomial.C_pow, hcd, ← hc', coe_frobeniusEquiv, frobenius_def]
  rw [← Φ_injective p this]
  refine (isUnit_iff_B _).2 ⟨c', ?_, rfl⟩
  rintro rfl
  rw [map_zero] at hc'
  exact hc hc'.symm

/-- If `N ∣ dt N` then `dt N = 0` (compare `t`-degrees of the coefficients). -/
lemma dt_eq_zero_of_dvd {N : Polynomial (Polynomial F)} (h : N ∣ dt N) : dt N = 0 := by
  by_contra hne
  obtain ⟨g, hg⟩ := h
  have hN0 : N ≠ 0 := by rintro rfl; simp at hne
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg; exact hne hg
  have hdeg : g.natDegree = 0 := by
    have h1 := natDegree_dt_le N
    rw [hg, Polynomial.natDegree_mul hN0 hg0] at h1
    omega
  obtain ⟨c, rfl⟩ : ∃ c : Polynomial F, g = C c := ⟨_, Polynomial.eq_C_of_natDegree_eq_zero hdeg⟩
  have hc0 : c ≠ 0 := by rintro rfl; simp at hg0
  -- pick a nonzero coefficient of `N`
  obtain ⟨i, hi⟩ : ∃ i, N.coeff i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hN0 (Polynomial.ext (fun i => by rw [hcon i, Polynomial.coeff_zero]))
  have hcoeff : Polynomial.derivative (N.coeff i) = N.coeff i * c := by
    have := congrArg (fun q => Polynomial.coeff q i) hg
    simpa [Polynomial.coeff_mul_C] using this
  have hlt : (Polynomial.derivative (N.coeff i)).natDegree < (N.coeff i * c).natDegree := by
    rw [Polynomial.natDegree_mul hi hc0]
    rcases Nat.eq_zero_or_pos (N.coeff i).natDegree with h0 | hpos
    · -- constant coefficient: derivative is zero but product is nonzero
      exfalso
      have hd : Polynomial.derivative (N.coeff i) = 0 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0]; simp
      rw [hd] at hcoeff
      exact mul_ne_zero hi hc0 hcoeff.symm
    · have := Polynomial.natDegree_derivative_lt (p := N.coeff i) hpos.ne'
      omega
  rw [hcoeff] at hlt
  exact lt_irrefl _ hlt

lemma dt_eq_zero_of_isRelPrime {N D : Polynomial (Polynomial F)} (hND : IsRelPrime N D)
    (h : dt N * D = N * dt D) : dt N = 0 ∧ dt D = 0 := by
  constructor
  · apply dt_eq_zero_of_dvd
    exact hND.dvd_of_dvd_mul_right ⟨dt D, h⟩
  · apply dt_eq_zero_of_dvd
    exact hND.symm.dvd_of_dvd_mul_right ⟨dt N, by rw [mul_comm, ← h, mul_comm]⟩

/-! ### The differential identity (★) from the evaluation identities -/

/-- For `τ ≠ 0`: `x = y * τ ^ n` (integer power) iff `x * τ ^ (−n)⁺ = y * τ ^ n⁺`. -/
lemma zpow_rel_iff {K : Type*} [Field K] {x y τ : K} (hτ : τ ≠ 0) (n : ℤ) :
    x = y * τ ^ n ↔ x * τ ^ (-n).toNat = y * τ ^ n.toNat := by
  rcases le_or_gt 0 n with hn | hn
  · have h1 : (-n).toNat = 0 := by omega
    have h2 : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    have h3 : τ ^ n = τ ^ n.toNat := by
      conv_lhs => rw [← h2]
      exact zpow_natCast τ n.toNat
    rw [h1, pow_zero, mul_one, h3]
  · have h1 : n.toNat = 0 := by omega
    have h2 : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    rw [h1, pow_zero, mul_one]
    constructor
    · intro h
      rw [h, mul_assoc, ← zpow_natCast, h2, ← zpow_add₀ hτ, add_neg_cancel, zpow_zero, mul_one]
    · intro h
      rw [← h, mul_assoc, ← zpow_natCast, h2, ← zpow_add₀ hτ, neg_add_cancel, zpow_zero, mul_one]

/-- The polynomial identity (★): if `N(a) = D(a) · τ_a^n` for all `a` in a large set `A`
(`τ_a = t + a^{p^k}`), then `f_k · (N' D − N D') = n · N D` in `F[t][X]`. -/
lemma star_identity [Fintype F] (k : ℕ) (n : ℤ) (N D : Polynomial (Polynomial F)) (A : Finset F)
    (hcard : p ^ k + N.natDegree + D.natDegree < A.card)
    (hrel : ∀ a ∈ A, N.eval (C a) * (Polynomial.X + C (a ^ p ^ k)) ^ (-n).toNat =
      D.eval (C a) * (Polynomial.X + C (a ^ p ^ k)) ^ n.toNat) :
    fk p k * (dt N * D - N * dt D) = (n : Polynomial (Polynomial F)) * (N * D) := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : Polynomial (Polynomial F),
      G = fk p k * (dt N * D - N * dt D) - (n : Polynomial (Polynomial F)) * (N * D) := ⟨_, rfl⟩
  have hdeg : G.natDegree < A.card := by
    rw [hG]
    have h1 : (fk p k * (dt N * D - N * dt D)).natDegree ≤ p ^ k + (N.natDegree + D.natDegree) := by
      refine (Polynomial.natDegree_mul_le).trans (add_le_add (fk_natDegree p k).le ?_)
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact Polynomial.natDegree_mul_le.trans (add_le_add (natDegree_dt_le N) le_rfl)
      · exact Polynomial.natDegree_mul_le.trans (add_le_add le_rfl (natDegree_dt_le D))
    have h2 : ((n : Polynomial (Polynomial F)) * (N * D)).natDegree ≤ N.natDegree + D.natDegree := by
      refine Polynomial.natDegree_mul_le.trans ?_
      rw [Polynomial.natDegree_intCast, zero_add]
      exact Polynomial.natDegree_mul_le
    have := (Polynomial.natDegree_sub_le _ _).trans (max_le h1 (h2.trans (Nat.le_add_left _ _)))
    omega
  have hzero : ∀ a : A, G.eval (C (a : F)) = 0 := by
    rintro ⟨a, ha⟩
    have hr := hrel a ha
    rw [hG]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_intCast, eval_C_fk,
      ← derivative_eval_C]
    obtain ⟨τ, hτ⟩ : ∃ τ : Polynomial F, τ = Polynomial.X + C (a ^ p ^ k) := ⟨_, rfl⟩
    rw [← hτ] at hr ⊢
    have hτ0 : τ ≠ 0 := by rw [hτ]; exact Polynomial.X_add_C_ne_zero _
    obtain ⟨Na, hNa⟩ : ∃ Na : Polynomial F, Na = N.eval (C a) := ⟨_, rfl⟩
    obtain ⟨Da, hDa⟩ : ∃ Da : Polynomial F, Da = D.eval (C a) := ⟨_, rfl⟩
    rw [← hNa, ← hDa] at hr ⊢
    -- multiply the relation by `τ` and differentiate: no `m - 1` appears
    have hr' : Na * τ ^ ((-n).toNat + 1) = Da * τ ^ (n.toNat + 1) := by
      rw [pow_succ, pow_succ, ← mul_assoc, ← mul_assoc, hr]
    have hd' := congrArg Polynomial.derivative hr'
    rw [Polynomial.derivative_mul, Polynomial.derivative_mul, hτ,
      Polynomial.derivative_X_add_C_pow, Polynomial.derivative_X_add_C_pow, ← hτ,
      Nat.add_sub_cancel, Nat.add_sub_cancel, Polynomial.C_eq_natCast, Polynomial.C_eq_natCast]
      at hd'
    have hn : (n : Polynomial F) =
        ((n.toNat : ℕ) : Polynomial F) - (((-n).toNat : ℕ) : Polynomial F) := by
      have := Int.toNat_sub_toNat_neg n
      conv_lhs => rw [← this]
      push_cast
      ring
    have key : (τ * (Polynomial.derivative Na * Da - Na * Polynomial.derivative Da) -
        (n : Polynomial F) * (Na * Da)) * (τ ^ (-n).toNat * τ ^ n.toNat) = 0 := by
      rw [hn]
      push_cast at hd' ⊢
      linear_combination (Da * τ ^ n.toNat) * hd' -
        (τ * Polynomial.derivative Da * τ ^ n.toNat +
          ((n.toNat : Polynomial F) + 1) * Da * τ ^ n.toNat) * hr
    have hne : τ ^ (-n).toNat * τ ^ n.toNat ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hτ0) (pow_ne_zero _ hτ0)
    exact (mul_eq_zero.1 key).resolve_right hne
  have hG0 : G = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero G
      (f := fun a : A => (C (a : F) : Polynomial F))
      (fun a b h => Subtype.ext (Polynomial.C_injective h)) hzero (by simpa using hdeg)
  rw [hG] at hG0
  exact sub_eq_zero.1 hG0

/-- Case C of the reconstruction step: if `f_k` divides neither `N` nor `D`, then (★) forces
`p ∣ n` and `N' D = N D'`. -/
lemma of_star_not_dvd (k : ℕ) (n : ℤ) {N D : Polynomial (Polynomial F)}
    (hN : ¬ fk p k ∣ N) (hD : ¬ fk p k ∣ D)
    (hstar : fk p k * (dt N * D - N * dt D) = (n : Polynomial (Polynomial F)) * (N * D)) :
    (p : ℤ) ∣ n ∧ dt N * D = N * dt D := by
  have hprime := fk_prime (F := F) p k
  have hdvd : fk p k ∣ (n : Polynomial (Polynomial F)) * (N * D) := ⟨_, hstar.symm⟩
  have hn : (n : Polynomial (Polynomial F)) = 0 := by
    rcases hprime.dvd_or_dvd hdvd with h | h
    · -- `f_k ∣ n`: `n` is a constant, hence zero
      by_contra hne
      have hunit : IsUnit (n : Polynomial (Polynomial F)) := by
        have : (n : Polynomial (Polynomial F)) = C (C (n : F)) := by
          rw [Polynomial.C_eq_intCast, Polynomial.C_eq_intCast]
        rw [this]
        refine (isUnit_iff_B _).2 ⟨(n : F), ?_, rfl⟩
        intro h0
        apply hne
        rw [this, h0, map_zero, map_zero]
      exact hprime.not_unit (isUnit_of_dvd_unit h hunit)
    · rcases hprime.dvd_or_dvd h with h' | h'
      · exact absurd h' hN
      · exact absurd h' hD
  refine ⟨?_, ?_⟩
  · have : ((n : ℤ) : F) = 0 := by
      have := congrArg (fun q => (q.coeff 0).coeff 0) hn
      simpa using this
    exact (CharP.intCast_eq_zero_iff F p n).1 this
  · rw [hn, zero_mul] at hstar
    rcases mul_eq_zero.1 hstar with h | h
    · exact absurd h (fk_ne_zero p k)
    · exact sub_eq_zero.1 h

end ArithDyn.Derksen
