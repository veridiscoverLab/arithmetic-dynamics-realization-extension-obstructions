import ArithDyn.Derksen.Frobenius

/-!
# The Frobenius reconstruction lemma (paper Lemma 2.5)

Let `F = 𝔽_q`, `q = p^e`, `B = F[t][X]`. Suppose `N, D ∈ B` are coprime, `D ≠ 0`, and for all `a`
in a set `A ⊆ F` with `|A| > p^{e-1} + deg_X N + deg_X D` we have `N(a) = D(a) · (t + a^{p^k})^n`
in `F(t)` (`n ∈ ℤ`, `0 ≤ k < e`). Then
`N/D = ∏_j (X^{p^{(k+j) mod e}} + t^{p^j})^{g_j}` and `n = ∑_j g_j p^j` for finitely supported
integers `g_j` (`reconstruct_aux`). The proof is a well-founded induction on
`(deg_X N + deg_X D, |n|)`: either `f_k = X^{p^k} + t` divides `N` or `D` (strip it, `n ↦ n ∓ 1`,
the height drops), or the differential identity (★) forces `p ∣ n`, `∂_t N = ∂_t D = 0`, and one
descends along the coefficientwise Frobenius (`n ↦ n/p`, phase `k ↦ k + 1 mod e`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ArithDyn.Derksen

open Polynomial

variable {F : Type*} [Field F] [Fintype F] (p e : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

-- `K` is any field of fractions of `F[t]` (e.g. `RatFunc F`).
variable {K : Type*} [Field K] [Algebra (Polynomial F) K] [IsFractionRing (Polynomial F) K]

/-- `F(t)(X) = Frac(F[t][X])`. -/
abbrev ΩB (F : Type*) [Field F] := FractionRing (Polynomial (Polynomial F))

variable (F) in
/-- The factor `X^{p^{(k+j) mod e}} + t^{p^j}`. -/
noncomputable def factor (k j : ℕ) : Polynomial (Polynomial F) :=
  X ^ (p ^ ((k + j) % e)) + C (Polynomial.X ^ (p ^ j))

lemma factor_monic (k j : ℕ) : (factor F p e k j).Monic := by
  unfold factor
  apply Polynomial.Monic.add_of_left (Polynomial.monic_X_pow _)
  rw [Polynomial.degree_X_pow]
  exact lt_of_le_of_lt Polynomial.degree_C_le
    (by exact_mod_cast pow_pos (Fact.out : p.Prime).pos _)

lemma factor_ne_zero (k j : ℕ) : (factor F p e k j) ≠ 0 := (factor_monic p e k j).ne_zero

lemma factor_zero {k : ℕ} (hk : k < e) : factor F p e k 0 = fk p k := by
  simp [factor, fk, Nat.mod_eq_of_lt hk]

lemma Φ_factor (k j : ℕ) : Φ p (factor F p e ((k + 1) % e) j) = factor F p e k (j + 1) := by
  unfold factor
  rw [map_add, map_pow, Φ_X, Φ_C, ← pow_mul, ← pow_succ]
  have : ((k + 1) % e + j) % e = (k + (j + 1)) % e := by
    rw [Nat.add_mod ((k + 1) % e) j e, Nat.mod_mod, ← Nat.add_mod]
    congr 1
    ring
  rw [this]

/-! ### Bookkeeping for the exponent vectors -/

/-- Adjusting the exponent at index `0` by `δ`. -/
lemma shift_at_zero {Ω : Type*} [Field Ω] (Fj : ℕ → Ω) (hF0 : Fj 0 ≠ 0) (J : ℕ) (g : ℕ → ℤ)
    (hsupp : ∀ j, J ≤ j → g j = 0) (m : ℤ) (R : Ω) (δ : ℤ)
    (hsum : m = ∑ j ∈ Finset.range J, g j * (p : ℤ) ^ j)
    (hprod : R = ∏ j ∈ Finset.range J, Fj j ^ g j) :
    ∃ (J' : ℕ) (g' : ℕ → ℤ), (∀ j, J' ≤ j → g' j = 0) ∧
      m + δ = ∑ j ∈ Finset.range J', g' j * (p : ℤ) ^ j ∧
      R * Fj 0 ^ δ = ∏ j ∈ Finset.range J', Fj j ^ g' j := by
  classical
  refine ⟨max J 1, Function.update g 0 (g 0 + δ), ?_, ?_, ?_⟩
  · intro j hj
    have hj0 : j ≠ 0 := by omega
    rw [Function.update_of_ne hj0]
    exact hsupp j (by omega)
  · have h0 : (0 : ℕ) ∈ Finset.range (max J 1) := by simp
    rw [← Finset.add_sum_erase _ _ h0, Function.update_self, pow_zero, mul_one]
    have hrest : ∑ j ∈ (Finset.range (max J 1)).erase 0, Function.update g 0 (g 0 + δ) j * (p : ℤ) ^ j =
        ∑ j ∈ (Finset.range (max J 1)).erase 0, g j * (p : ℤ) ^ j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj0 : j ≠ 0 := (Finset.mem_erase.1 hj).1
      rw [Function.update_of_ne hj0]
    rw [hrest, hsum]
    have hsub : Finset.range J ⊆ Finset.range (max J 1) := Finset.range_mono (le_max_left _ _)
    rw [Finset.sum_subset hsub (fun j hj hj' => by
      rw [hsupp j (by simpa using hj'), zero_mul])]
    rw [← Finset.add_sum_erase _ _ h0, pow_zero, mul_one]
    ring
  · have h0 : (0 : ℕ) ∈ Finset.range (max J 1) := by simp
    rw [← Finset.mul_prod_erase _ _ h0, Function.update_self]
    have hrest : ∏ j ∈ (Finset.range (max J 1)).erase 0, Fj j ^ Function.update g 0 (g 0 + δ) j =
        ∏ j ∈ (Finset.range (max J 1)).erase 0, Fj j ^ g j := by
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hj0 : j ≠ 0 := (Finset.mem_erase.1 hj).1
      rw [Function.update_of_ne hj0]
    rw [hrest, hprod]
    have hsub : Finset.range J ⊆ Finset.range (max J 1) := Finset.range_mono (le_max_left _ _)
    rw [Finset.prod_subset hsub (fun j hj hj' => by
      rw [hsupp j (by simpa using hj'), zpow_zero])]
    rw [← Finset.mul_prod_erase _ _ h0, zpow_add₀ hF0]
    ring

/-- Shifting all exponents up by one (index `0` gets exponent `0`). -/
lemma shift_succ {Ω : Type*} [Field Ω] (Fj : ℕ → Ω) (J : ℕ) (g : ℕ → ℤ)
    (hsupp : ∀ j, J ≤ j → g j = 0) (m : ℤ) (R : Ω)
    (hsum : m = ∑ j ∈ Finset.range J, g j * (p : ℤ) ^ j)
    (hprod : R = ∏ j ∈ Finset.range J, Fj (j + 1) ^ g j) :
    ∃ (J' : ℕ) (g' : ℕ → ℤ), (∀ j, J' ≤ j → g' j = 0) ∧
      (p : ℤ) * m = ∑ j ∈ Finset.range J', g' j * (p : ℤ) ^ j ∧
      R = ∏ j ∈ Finset.range J', Fj j ^ g' j := by
  refine ⟨J + 1, fun j => if j = 0 then 0 else g (j - 1), ?_, ?_, ?_⟩
  · intro j hj
    have hj0 : j ≠ 0 := by omega
    simp only [if_neg hj0]
    exact hsupp (j - 1) (by omega)
  · rw [Finset.sum_range_succ', hsum, Finset.mul_sum]
    have h1 : ∀ j : ℕ, (if j + 1 = 0 then (0 : ℤ) else g (j + 1 - 1)) = g j := by
      intro j; rw [if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
    simp only [h1, if_pos, pow_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pow_succ]; ring
  · rw [Finset.prod_range_succ', hprod]
    have h1 : ∀ j : ℕ, (if j + 1 = 0 then (0 : ℤ) else g (j + 1 - 1)) = g j := by
      intro j; rw [if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
    simp only [h1, if_pos, zpow_zero, mul_one]

/-! ### Small auxiliary facts -/

lemma pow_p_pow_mod (hq : Fintype.card F = p ^ e) (a : F) {k : ℕ} (hk : k < e) :
    a ^ p ^ (k + 1) = a ^ p ^ ((k + 1) % e) := by
  rcases Nat.lt_or_ge (k + 1) e with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have h' : k + 1 = e := by omega
    rw [h', Nat.mod_self, pow_zero, pow_one, ← hq, FiniteField.pow_card]

lemma pow_p_injective {K : Type*} [CommRing K] [IsDomain K] [CharP K p] {x y : K}
    (h : x ^ p = y ^ p) : x = y := by
  have : (x - y) ^ p = 0 := by rw [sub_pow_char, h, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 this)

lemma τK_ne_zero (a : F) (k : ℕ) :
    algebraMap (Polynomial F) K (Polynomial.X + C (a ^ p ^ k)) ≠ 0 := by
  rw [Ne, IsFractionRing.to_map_eq_zero_iff]
  exact Polynomial.X_add_C_ne_zero _

/-- The coefficientwise Frobenius, extended to `Frac(F[t][X])`. -/
noncomputable def Φ' : ΩB F →+* ΩB F :=
  IsLocalization.map (ΩB F) (Φ (F := F) p) (M := nonZeroDivisors (Polynomial (Polynomial F)))
    (T := nonZeroDivisors (Polynomial (Polynomial F)))
    (fun x hx => by
      rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at *
      exact (map_ne_zero_iff _ (Φ_injective p)).2 hx)

lemma Φ'_algebraMap (N : Polynomial (Polynomial F)) :
    Φ' p (algebraMap _ (ΩB F) N) = algebraMap _ (ΩB F) (Φ p N) :=
  IsLocalization.map_eq _ _

/-! ### The main induction -/

set_option maxHeartbeats 1600000 in
/-- **Lemma 2.5, inductive form.** -/
theorem reconstruct_aux (hq : Fintype.card F = p ^ e) (he : 1 ≤ e) :
    ∀ (h : ℕ) (m : ℕ) (k : ℕ) (n : ℤ) (N D : Polynomial (Polynomial F)) (A : Finset F),
      k < e → IsRelPrime N D → D ≠ 0 → N.natDegree + D.natDegree = h → n.natAbs = m →
      p ^ (e - 1) + h < A.card →
      (∀ a ∈ A, algebraMap _ K (N.eval (C a)) =
        algebraMap _ K (D.eval (C a)) *
          algebraMap _ K (Polynomial.X + C (a ^ p ^ k)) ^ n) →
      ∃ (J : ℕ) (g : ℕ → ℤ), (∀ j, J ≤ j → g j = 0) ∧
        n = ∑ j ∈ Finset.range J, g j * (p : ℤ) ^ j ∧
        algebraMap _ (ΩB F) N / algebraMap _ (ΩB F) D =
          ∏ j ∈ Finset.range J, algebraMap _ (ΩB F) (factor F p e k j) ^ g j := by
  classical
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ihh =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro k n N D A hk hND hD hh hm hcard hrel
  have hιB : Function.Injective (algebraMap (Polynomial (Polynomial F)) (ΩB F)) :=
    IsFractionRing.injective (Polynomial (Polynomial F)) (ΩB F)
  have hιK : Function.Injective (algebraMap (Polynomial F) K) :=
    IsFractionRing.injective (Polynomial F) K
  have hDΩ : algebraMap _ (ΩB F) D ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hD
  have hAne : A.Nonempty := Finset.card_pos.1 (by omega)
  -- Base case `n = 0`
  by_cases hn0 : n = 0
  · subst hn0
    have heq : N = D := by
      have hz : ∀ a : A, (N - D).eval (C (a : F)) = 0 := by
        rintro ⟨a, ha⟩
        have := hrel a ha
        rw [zpow_zero, mul_one] at this
        rw [Polynomial.eval_sub, sub_eq_zero]
        exact hιK this
      have hdeg : (N - D).natDegree < A.card := by
        have h1 := Polynomial.natDegree_sub_le N D
        have h2 : max N.natDegree D.natDegree ≤ h := by
          rw [← hh]; exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
        omega
      have := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (N - D)
        (f := fun a : A => (C (a : F) : Polynomial F))
        (fun a b h => Subtype.ext (Polynomial.C_injective h)) hz (by simpa using hdeg)
      exact sub_eq_zero.1 this
    refine ⟨0, fun _ => 0, fun _ _ => rfl, by simp, ?_⟩
    rw [heq, div_self hDΩ]
    simp
  -- `N ≠ 0`
  have hN0 : N ≠ 0 := by
    rintro rfl
    have hu : IsUnit D := isRelPrime_zero_left.1 hND
    obtain ⟨c, hc, rfl⟩ := (isUnit_iff_B D).1 hu
    obtain ⟨a, ha⟩ := hAne
    have := hrel a ha
    rw [Polynomial.eval_zero, map_zero, Polynomial.eval_C] at this
    refine mul_ne_zero ?_ (zpow_ne_zero _ (τK_ne_zero (K := K) p a k)) this.symm
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact Polynomial.C_ne_zero.2 hc
  have hpk : 0 < p ^ k := pow_pos (Fact.out : p.Prime).pos k
  by_cases hAN : fk p k ∣ N
  · -- Case A: strip `f_k` from `N`
    obtain ⟨N₁, rfl⟩ := hAN
    have hN₁0 : N₁ ≠ 0 := by rintro rfl; simp at hN0
    have hND₁ : IsRelPrime N₁ D := hND.of_dvd_left (dvd_mul_left _ _)
    have hdeg₁ : N₁.natDegree + D.natDegree < h := by
      rw [← hh, Polynomial.natDegree_mul (fk_ne_zero p k) hN₁0, fk_natDegree]
      omega
    have hrel₁ : ∀ a ∈ A, algebraMap _ K (N₁.eval (C a)) =
        algebraMap _ K (D.eval (C a)) *
          algebraMap _ K (Polynomial.X + C (a ^ p ^ k)) ^ (n - 1) := by
      intro a ha
      have h1 := hrel a ha
      rw [Polynomial.eval_mul, eval_C_fk, map_mul] at h1
      have hτ := τK_ne_zero (K := K) p a k
      rw [zpow_sub_one₀ hτ]
      field_simp
      linear_combination h1
    obtain ⟨J, g, hsupp, hsum, hprod⟩ :=
      ihh _ hdeg₁ (n - 1).natAbs k (n - 1) N₁ D A hk hND₁ hD rfl rfl (by omega) hrel₁
    have hF0 : algebraMap _ (ΩB F) (factor F p e k 0) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact factor_ne_zero p e k 0
    obtain ⟨J', g', hsupp', hsum', hprod'⟩ := shift_at_zero p
      (fun j => algebraMap _ (ΩB F) (factor F p e k j)) hF0 J g hsupp (n - 1)
      (algebraMap _ (ΩB F) N₁ / algebraMap _ (ΩB F) D) 1 hsum hprod
    refine ⟨J', g', hsupp', by rw [← hsum']; ring, ?_⟩
    rw [← hprod', factor_zero p e hk, map_mul, zpow_one]
    field_simp
  by_cases hAD : fk p k ∣ D
  · -- Case B: strip `f_k` from `D`
    obtain ⟨D₁, rfl⟩ := hAD
    have hD₁0 : D₁ ≠ 0 := by rintro rfl; simp at hD
    have hND₁ : IsRelPrime N D₁ := hND.of_dvd_right (dvd_mul_left _ _)
    have hdeg₁ : N.natDegree + D₁.natDegree < h := by
      rw [← hh, Polynomial.natDegree_mul (fk_ne_zero p k) hD₁0, fk_natDegree]
      omega
    have hrel₁ : ∀ a ∈ A, algebraMap _ K (N.eval (C a)) =
        algebraMap _ K (D₁.eval (C a)) *
          algebraMap _ K (Polynomial.X + C (a ^ p ^ k)) ^ (n + 1) := by
      intro a ha
      have h1 := hrel a ha
      rw [Polynomial.eval_mul, eval_C_fk, map_mul] at h1
      have hτ := τK_ne_zero (K := K) p a k
      rw [zpow_add_one₀ hτ]
      linear_combination h1
    obtain ⟨J, g, hsupp, hsum, hprod⟩ :=
      ihh _ hdeg₁ (n + 1).natAbs k (n + 1) N D₁ A hk hND₁ hD₁0 rfl rfl (by omega) hrel₁
    have hF0 : algebraMap _ (ΩB F) (factor F p e k 0) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact factor_ne_zero p e k 0
    obtain ⟨J', g', hsupp', hsum', hprod'⟩ := shift_at_zero p
      (fun j => algebraMap _ (ΩB F) (factor F p e k j)) hF0 J g hsupp (n + 1)
      (algebraMap _ (ΩB F) N / algebraMap _ (ΩB F) D₁) (-1) hsum hprod
    refine ⟨J', g', hsupp', by rw [← hsum']; ring, ?_⟩
    rw [← hprod', factor_zero p e hk, map_mul, zpow_neg_one]
    have hD₁Ω : algebraMap _ (ΩB F) D₁ ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hD₁0
    rw [factor_zero p e hk] at hF0
    field_simp
  -- Case C: Frobenius descent
  have hrelP : ∀ a ∈ A, N.eval (C a) * (Polynomial.X + C (a ^ p ^ k)) ^ (-n).toNat =
      D.eval (C a) * (Polynomial.X + C (a ^ p ^ k)) ^ n.toNat := by
    intro a ha
    have h1 := hrel a ha
    rw [zpow_rel_iff (τK_ne_zero (K := K) p a k) n] at h1
    apply hιK
    simpa only [map_mul, map_pow] using h1
  have hcard' : p ^ k + N.natDegree + D.natDegree < A.card := by
    have : p ^ k ≤ p ^ (e - 1) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    omega
  have hstar := star_identity p k n N D A hcard' hrelP
  obtain ⟨hpn, hlog⟩ := of_star_not_dvd p k n hAN hAD hstar
  obtain ⟨hdN, hdD⟩ := dt_eq_zero_of_isRelPrime hND hlog
  obtain ⟨N'', rfl⟩ := exists_Φ_eq p N hdN
  obtain ⟨D'', rfl⟩ := exists_Φ_eq p D hdD
  obtain ⟨n', rfl⟩ := hpn
  have hn'0 : n' ≠ 0 := by rintro rfl; simp at hn0
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hlt : n'.natAbs < m := by
    rw [← hm, Int.natAbs_mul, Int.natAbs_natCast]
    have : 0 < n'.natAbs := Int.natAbs_pos.2 hn'0
    nlinarith
  obtain ⟨k', hk'def⟩ : ∃ k', k' = (k + 1) % e := ⟨_, rfl⟩
  have hk' : k' < e := by rw [hk'def]; exact Nat.mod_lt _ (by omega)
  obtain ⟨A', hA'def⟩ : ∃ A' : Finset F, A' = A.image (frobeniusEquiv F p).symm := ⟨_, rfl⟩
  have hA'card : A'.card = A.card := by
    rw [hA'def]; exact Finset.card_image_of_injective _ (frobeniusEquiv F p).symm.injective
  have hmemA' : ∀ a, a ∈ A' → a ^ p ∈ A := by
    intro a ha
    rw [hA'def, Finset.mem_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have : ((frobeniusEquiv F p).symm b) ^ p = b := by
      rw [← frobenius_def, ← coe_frobeniusEquiv, RingEquiv.apply_symm_apply]
    rw [this]; exact hb
  have hND'' : IsRelPrime N'' D'' := isRelPrime_of_Φ p hND
  have hD''0 : D'' ≠ 0 := by rintro rfl; simp at hD
  have hh'' : N''.natDegree + D''.natDegree = h := by rw [← hh, natDegree_Φ, natDegree_Φ]
  haveI : CharP K p := charP_of_injective_algebraMap hιK p
  have hrel'' : ∀ a ∈ A', algebraMap _ K (N''.eval (C a)) =
      algebraMap _ K (D''.eval (C a)) *
        algebraMap _ K (Polynomial.X + C (a ^ p ^ k')) ^ n' := by
    intro a ha
    have h1 := hrel (a ^ p) (hmemA' a ha)
    rw [eval_Φ, eval_Φ, map_pow, map_pow] at h1
    have hτeq : (a ^ p) ^ p ^ k = a ^ p ^ k' := by
      rw [← pow_mul, ← pow_succ', hk'def, pow_p_pow_mod p e hq a hk]
    rw [hτeq] at h1
    apply pow_p_injective p
    rw [mul_pow, h1, ← zpow_natCast (algebraMap _ K (Polynomial.X + C (a ^ p ^ k')) ^ n'),
      ← zpow_mul, mul_comm n']
  obtain ⟨J, g, hsupp, hsum, hprod⟩ :=
    ihm n'.natAbs hlt k' n' N'' D'' A' hk' hND'' hD''0 hh'' rfl (by rw [hA'card]; exact hcard) hrel''
  -- transport along `Φ'`
  have hΦprod : algebraMap _ (ΩB F) (Φ p N'') / algebraMap _ (ΩB F) (Φ p D'') =
      ∏ j ∈ Finset.range J, algebraMap _ (ΩB F) (factor F p e k (j + 1)) ^ g j := by
    have := congrArg (Φ' p) hprod
    rw [map_div₀, Φ'_algebraMap, Φ'_algebraMap, map_prod] at this
    rw [this]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [map_zpow₀, Φ'_algebraMap, hk'def, Φ_factor]
  obtain ⟨J', g', hsupp', hsum', hprod'⟩ := shift_succ p
    (fun j => algebraMap _ (ΩB F) (factor F p e k j)) J g hsupp n' _ hsum hΦprod
  exact ⟨J', g', hsupp', hsum', hprod'⟩

/-! ### Phase `0`, arbitrary `N, D`, and regrouping by powers of `q` -/

lemma zpow_sum₀ {G : Type*} [CommGroupWithZero G] {a : G} (ha : a ≠ 0) {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) : a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

lemma factor_zero_eq (j : ℕ) :
    factor F p e 0 j = (X + C (Polynomial.X ^ (p ^ e) ^ (j / e))) ^ (p ^ (j % e)) := by
  unfold factor
  rw [zero_add, add_pow_char_pow, ← Polynomial.C_pow, ← pow_mul, ← pow_mul, ← pow_add,
    Nat.div_add_mod]

set_option maxHeartbeats 800000 in
/-- **Lemma 2.5.** For `N, D ∈ F[t][X]`, `D ≠ 0`, and a set `A ⊆ F` with
`p^{e-1} + deg N + deg D < |A|` such that `N(a) = D(a) (t + a)^n` for `a ∈ A`, there
are finitely supported integers `d_ℓ` with `n = ∑_ℓ d_ℓ q^ℓ` and `N/D = ∏_ℓ (X + t^{q^ℓ})^{d_ℓ}`. -/
theorem reconstruct (hq : Fintype.card F = p ^ e) (he : 1 ≤ e) (n : ℤ)
    (N D : Polynomial (Polynomial F)) (A : Finset F) (hD : D ≠ 0)
    (hcard : p ^ (e - 1) + N.natDegree + D.natDegree < A.card)
    (hrel : ∀ a ∈ A, algebraMap _ K (N.eval (C a)) =
      algebraMap _ K (D.eval (C a)) * algebraMap _ K (Polynomial.X + C a) ^ n) :
    ∃ (L : ℕ) (d : ℕ → ℤ), (∀ ℓ, L ≤ ℓ → d ℓ = 0) ∧
      n = ∑ ℓ ∈ Finset.range L, d ℓ * ((p ^ e : ℕ) : ℤ) ^ ℓ ∧
      algebraMap _ (ΩB F) N / algebraMap _ (ΩB F) D =
        ∏ ℓ ∈ Finset.range L,
          algebraMap _ (ΩB F) (X + C (Polynomial.X ^ (p ^ e) ^ ℓ) : Polynomial (Polynomial F)) ^ d ℓ := by
  classical
  letI : GCDMonoid (Polynomial (Polynomial F)) := UniqueFactorizationMonoid.toGCDMonoid _
  obtain ⟨N₁, D₁, hN₁, hD₁, hu⟩ := extract_gcd N D
  have hND₁ : IsRelPrime N₁ D₁ := gcd_isUnit_iff_isRelPrime.1 hu
  obtain ⟨g, hg⟩ : ∃ g, g = gcd N D := ⟨_, rfl⟩
  rw [← hg] at hN₁ hD₁
  have hg0 : g ≠ 0 := by rintro rfl; rw [zero_mul] at hD₁; exact hD hD₁
  have hD₁0 : D₁ ≠ 0 := by rintro rfl; rw [mul_zero] at hD₁; exact hD hD₁
  have hdegD : D₁.natDegree + g.natDegree = D.natDegree := by
    rw [hD₁, Polynomial.natDegree_mul hg0 hD₁0]; ring
  have hdegN : N₁.natDegree ≤ N.natDegree := by
    rcases eq_or_ne N₁ 0 with h | h
    · simp [h]
    · rw [hN₁, Polynomial.natDegree_mul hg0 h]; omega
  -- the points where `g` does not vanish
  obtain ⟨A', hA'⟩ : ∃ A' : Finset F, A' = A.filter (fun a => g.eval (C a) ≠ 0) := ⟨_, rfl⟩
  have hA'card : A.card ≤ A'.card + g.natDegree := by
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := A)
      (fun a => g.eval (C a) ≠ 0)
    have hbad : (A.filter (fun a => ¬ g.eval (C a) ≠ 0)).card ≤ g.natDegree := by
      calc (A.filter (fun a => ¬ g.eval (C a) ≠ 0)).card
          ≤ g.roots.toFinset.card := by
            apply Finset.card_le_card_of_injOn (fun a => (C a : Polynomial F))
            · intro a ha
              rw [Finset.mem_coe, Finset.mem_filter, not_not] at ha
              rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hg0]
              exact ha.2
            · intro a _ b _ h
              exact Polynomial.C_injective h
        _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
        _ ≤ g.natDegree := Polynomial.card_roots' g
    rw [hA']
    omega
  have hcard' : p ^ (e - 1) + (N₁.natDegree + D₁.natDegree) < A'.card := by omega
  have hrel₁ : ∀ a ∈ A', algebraMap _ K (N₁.eval (C a)) =
      algebraMap _ K (D₁.eval (C a)) *
        algebraMap _ K (Polynomial.X + C (a ^ p ^ 0)) ^ n := by
    intro a ha
    rw [hA', Finset.mem_filter] at ha
    have h1 := hrel a ha.1
    rw [hN₁, hD₁, Polynomial.eval_mul, Polynomial.eval_mul, map_mul, map_mul] at h1
    have hga : algebraMap _ K (g.eval (C a)) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact ha.2
    rw [pow_zero, pow_one]
    exact mul_left_cancel₀ hga (by rw [h1]; ring)
  obtain ⟨J, gg, hsupp, hsum, hprod⟩ :=
    reconstruct_aux p e hq he _ _ 0 n N₁ D₁ A' (by omega) hND₁ hD₁0 rfl rfl hcard' hrel₁
  have hquot : algebraMap _ (ΩB F) N / algebraMap _ (ΩB F) D =
      algebraMap _ (ΩB F) N₁ / algebraMap _ (ΩB F) D₁ := by
    rw [hN₁, hD₁, map_mul, map_mul]
    have hgΩ : algebraMap _ (ΩB F) g ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hg0
    rw [mul_div_mul_left _ _ hgΩ]
  have hmaps : ∀ j ∈ Finset.range J, j / e ∈ Finset.range J := by
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    exact lt_of_le_of_lt (Nat.div_le_self j e) hj
  refine ⟨J, fun ℓ => ∑ j ∈ (Finset.range J).filter (fun j => j / e = ℓ),
    ((p ^ (j % e) : ℕ) : ℤ) * gg j, ?_, ?_, ?_⟩
  · intro ℓ hℓ
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    have : j / e ≤ j := Nat.div_le_self j e
    omega
  · rw [hsum, ← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_filter] at hj
    rw [← hj.2]
    have : (p : ℤ) ^ j = (p : ℤ) ^ (j % e) * ((p : ℤ) ^ e) ^ (j / e) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    push_cast
    rw [this]
    ring
  · rw [hquot, hprod, ← Finset.prod_fiberwise_of_maps_to hmaps]
    refine Finset.prod_congr rfl (fun ℓ _ => ?_)
    have hF : algebraMap _ (ΩB F) (X + C (Polynomial.X ^ (p ^ e) ^ ℓ) : Polynomial (Polynomial F)) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact Polynomial.X_add_C_ne_zero _
    rw [zpow_sum₀ hF]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finset.mem_filter] at hj
    rw [factor_zero_eq, map_pow, hj.2, ← zpow_natCast, ← zpow_mul]

end ArithDyn.Derksen
