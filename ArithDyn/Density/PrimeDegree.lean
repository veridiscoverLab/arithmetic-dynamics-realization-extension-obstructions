import ArithDyn.Density.MeanOrder

/-!
# Prime extension degrees (paper §4.3, proof of Proposition 4.7, (4.23)–(4.25))

`H Q ℓ = 1 + Q + ⋯ + Q^{ℓ-1}`, so `Q^ℓ - 1 = (Q-1) H`. For an odd prime `ℓ ∤ Q - 1`
every prime factor `r` of `H` satisfies `r ≥ 2ℓ + 1`, which gives the bounds
`∑_{r ∣ H} 1/r ≤ ω(H)/(2ℓ+1)` and `1 - ∑_{r∣H} 1/r ≤ 𝓜(H)`.
-/

set_option autoImplicit false

namespace ArithDyn

open Finset

/-- `H Q ℓ = ∑_{i<ℓ} Q^i` (4.23). -/
def H (Q ℓ : ℕ) : ℕ := ∑ i ∈ range ℓ, Q ^ i

lemma H_succ (Q ℓ : ℕ) : H Q (ℓ + 1) = H Q ℓ + Q ^ ℓ := sum_range_succ _ _

lemma H_pos (Q : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) : 0 < H Q ℓ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hℓ.ne'
  rw [H, sum_range_succ']
  simp

lemma sub_one_mul_H {Q : ℕ} (hQ : 2 ≤ Q) (ℓ : ℕ) : (Q - 1) * H Q ℓ = Q ^ ℓ - 1 := by
  rw [H, Nat.geomSum_eq hQ, Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one Q ℓ)]

lemma H_le_pow {Q : ℕ} (hQ : 2 ≤ Q) (ℓ : ℕ) : H Q ℓ ≤ Q ^ ℓ := by
  rw [H, Nat.geomSum_eq hQ]
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

lemma H_modEq (Q ℓ : ℕ) (hQ : 1 ≤ Q) : H Q ℓ ≡ ℓ [MOD Q - 1] := by
  have h1 : Q ≡ 1 [MOD Q - 1] := ((Nat.modEq_iff_dvd' hQ).2 dvd_rfl).symm
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [H_succ]
    have := h1.pow ℓ
    rw [one_pow] at this
    exact ih.add this

lemma coprime_H {Q ℓ : ℕ} (hQ : 2 ≤ Q) (hℓ : ℓ.Prime) (hnd : ¬ ℓ ∣ Q - 1) :
    Nat.Coprime (H Q ℓ) (Q - 1) := by
  rw [Nat.coprime_iff_gcd_eq_one, (H_modEq Q ℓ (by omega)).gcd_eq]
  exact (Nat.Prime.coprime_iff_not_dvd hℓ).2 hnd

lemma H_eq_one_add (Q : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) : H Q ℓ = 1 + Q * H Q (ℓ - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp only [H, Nat.add_sub_cancel, sum_range_succ', pow_zero, pow_succ, ← sum_mul]
  ring

/-- (4.24): every prime factor `r` of `H_ℓ` satisfies `r ≥ 2ℓ + 1`. -/
lemma prime_dvd_H_ge {Q ℓ r : ℕ} (hQ : 2 ≤ Q) (hℓ : ℓ.Prime) (hodd : Odd ℓ) (hnd : ¬ ℓ ∣ Q - 1)
    (hr : r.Prime) (hrH : r ∣ H Q ℓ) : 2 * ℓ + 1 ≤ r := by
  haveI := Fact.mk hr
  have hℓpos : 0 < ℓ := hℓ.pos
  have hr2 := hr.two_le
  -- `r ∤ Q`
  have hrQ : ¬ r ∣ Q := by
    intro hrQ
    have hH : H Q ℓ = Q * H Q (ℓ - 1) + 1 := by rw [H_eq_one_add Q hℓpos, add_comm]
    have h2 : r ∣ Q * H Q (ℓ - 1) := dvd_mul_of_dvd_left hrQ _
    have h1 : r ∣ 1 := (Nat.dvd_add_right h2).1 (hH ▸ hrH)
    exact hr.one_lt.ne' (Nat.dvd_one.1 h1)
  have hQ0 : (Q : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hrQ
  -- `Q^ℓ = 1` in `ZMod r`
  have hpow : (Q : ZMod r) ^ ℓ = 1 := by
    have hdvd : r ∣ Q ^ ℓ - 1 := hrH.trans (by rw [← sub_one_mul_H hQ ℓ]; exact dvd_mul_left _ _)
    have := (ZMod.natCast_eq_zero_iff (Q ^ ℓ - 1) r).2 hdvd
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at this
    exact this
  have hord : orderOf (Q : ZMod r) ∣ ℓ := orderOf_dvd_of_pow_eq_one hpow
  rcases hℓ.eq_one_or_self_of_dvd _ hord with h1 | h1
  · exfalso
    rw [orderOf_eq_one_iff] at h1
    have hr1 : r ∣ Q - 1 := by
      apply (ZMod.natCast_eq_zero_iff (Q - 1) r).1
      rw [Nat.cast_sub (by omega), Nat.cast_one, h1, sub_self]
    have hcop := coprime_H hQ hℓ hnd
    have : r ∣ Nat.gcd (H Q ℓ) (Q - 1) := Nat.dvd_gcd hrH hr1
    rw [hcop.gcd_eq_one] at this
    exact hr.one_lt.ne' (Nat.dvd_one.1 this)
  · have hℓr : ℓ ∣ r - 1 := by
      rw [← h1]; exact ZMod.orderOf_dvd_card_sub_one hQ0
    have hr2' : r ≠ 2 := by
      rintro rfl
      exact hℓ.one_lt.ne' (Nat.dvd_one.1 hℓr)
    have hrodd : Odd r := hr.odd_of_ne_two hr2'
    obtain ⟨k, hk⟩ := hℓr
    have hev : Even (r - 1) := by
      obtain ⟨m, hm⟩ := hrodd
      exact ⟨m, by omega⟩
    rw [hk, Nat.even_mul] at hev
    have hkeven : Even k := hev.resolve_left (Nat.not_even_iff_odd.2 hodd)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      omega
    obtain ⟨j, hj⟩ := hkeven
    have hj0 : 1 ≤ j := by omega
    have : 2 * ℓ ≤ r - 1 := by rw [hk, hj]; nlinarith
    omega

lemma pow_card_primeFactors_le {Q ℓ : ℕ} (hQ : 2 ≤ Q) (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hnd : ¬ ℓ ∣ Q - 1) : (2 * ℓ + 1) ^ (H Q ℓ).primeFactors.card ≤ H Q ℓ := by
  have hpos := H_pos Q hℓ.pos
  calc (2 * ℓ + 1) ^ (H Q ℓ).primeFactors.card ≤ ∏ r ∈ (H Q ℓ).primeFactors, r :=
        pow_card_le_prod _ _ _ (fun r hr => prime_dvd_H_ge hQ hℓ hodd hnd
          (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr))
    _ ≤ H Q ℓ := Nat.le_of_dvd hpos (Nat.prod_primeFactors_dvd _)

/-- `K₀ ω(H_ℓ) ≤ ℓ` as soon as `Q^{K₀} ≤ 2ℓ+1` (a log-free form of (4.25)). -/
lemma card_primeFactors_H_le {Q ℓ K₀ : ℕ} (hQ : 2 ≤ Q) (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hnd : ¬ ℓ ∣ Q - 1) (hK : Q ^ K₀ ≤ 2 * ℓ + 1) : K₀ * (H Q ℓ).primeFactors.card ≤ ℓ := by
  have h1 := pow_card_primeFactors_le hQ hℓ hodd hnd
  have h2 := H_le_pow hQ ℓ
  have h3 : (Q ^ K₀) ^ (H Q ℓ).primeFactors.card ≤ (2 * ℓ + 1) ^ (H Q ℓ).primeFactors.card :=
    Nat.pow_le_pow_left hK _
  rw [← pow_mul] at h3
  exact (Nat.pow_le_pow_iff_right (by omega)).1 (h3.trans (h1.trans h2))

lemma sum_inv_primeFactors_le {Q ℓ : ℕ} (hQ : 2 ≤ Q) (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hnd : ¬ ℓ ∣ Q - 1) :
    ∑ r ∈ (H Q ℓ).primeFactors, (1 / r : ℝ) ≤
      (H Q ℓ).primeFactors.card * (1 / (2 * (ℓ : ℝ) + 1)) := by
  have := Finset.sum_le_card_nsmul (H Q ℓ).primeFactors (fun r => (1 / r : ℝ))
    (1 / (2 * (ℓ : ℝ) + 1)) (fun r hr => by
      have h := prime_dvd_H_ge hQ hℓ hodd hnd (Nat.prime_of_mem_primeFactors hr)
        (Nat.dvd_of_mem_primeFactors hr)
      have h' : (2 * (ℓ : ℝ) + 1) ≤ r := by exact_mod_cast h
      exact one_div_le_one_div_of_le (by positivity) h')
  simpa using this

lemma card_div_le {ℓ K₀ c : ℕ} (hK₀ : 1 ≤ K₀) (h : K₀ * c ≤ ℓ) :
    (c : ℝ) * (1 / (2 * (ℓ : ℝ) + 1)) ≤ 1 / (2 * (K₀ : ℝ)) := by
  have hK : (0 : ℝ) < K₀ := by exact_mod_cast hK₀
  have h' : (K₀ : ℝ) * c ≤ ℓ := by exact_mod_cast h
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `∏ (1 - xᵢ) ≥ 1 - ∑ xᵢ` for `0 ≤ xᵢ ≤ 1`. -/
lemma one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have hxa0 := h0 a (mem_insert_self a s)
    have hxa1 := h1 a (mem_insert_self a s)
    have hs0 : 0 ≤ ∑ i ∈ s, x i := sum_nonneg (fun i hi => h0 i (mem_insert_of_mem hi))
    nlinarith [mul_nonneg hxa0 hs0, mul_le_mul_of_nonneg_left ih' (sub_nonneg.2 hxa1)]

lemma totient_div_eq_prod {n : ℕ} (hn : 0 < n) :
    (Nat.totient n : ℝ) / n = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := Nat.totient_eq_mul_prod_factors n
  have h' : ((Nat.totient n : ℚ) : ℝ) =
      (((n : ℚ) * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by rw [h]
  push_cast at h'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_eq_iff hn', h']
  simp only [one_div]
  ring

lemma M_H_ge {Q ℓ : ℕ} (hℓ : ℓ.Prime) :
    1 - ∑ r ∈ (H Q ℓ).primeFactors, (1 / r : ℝ) ≤ M (H Q ℓ) := by
  have hpos := H_pos Q hℓ.pos
  calc 1 - ∑ r ∈ (H Q ℓ).primeFactors, (1 / r : ℝ)
      ≤ ∏ r ∈ (H Q ℓ).primeFactors, (1 - 1 / (r : ℝ)) :=
        one_sub_sum_le_prod_one_sub _ _ (fun r _ => by positivity) (fun r hr => by
          have h1 : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).one_le
          exact (div_le_one (by positivity)).2 h1)
    _ = (Nat.totient (H Q ℓ) : ℝ) / H Q ℓ := (totient_div_eq_prod hpos).symm
    _ ≤ M (H Q ℓ) := totient_div_le_M hpos

lemma M_pow_sub_one_eq {Q ℓ : ℕ} (hQ : 2 ≤ Q) (hℓ : ℓ.Prime) (hnd : ¬ ℓ ∣ Q - 1) :
    M (Q ^ ℓ - 1) = M (Q - 1) * M (H Q ℓ) := by
  rw [← sub_one_mul_H hQ ℓ, M_mul (coprime_H hQ hℓ hnd).symm]

/-- The key estimate: `1 - 𝓜(Q^ℓ - 1) ≤ 1 - 𝓜(Q-1) + ∑_{r ∣ H_ℓ} 1/r`. -/
lemma one_sub_M_le {Q ℓ : ℕ} (hQ : 2 ≤ Q) (hℓ : ℓ.Prime) (hnd : ¬ ℓ ∣ Q - 1) :
    1 - M (Q ^ ℓ - 1) ≤ 1 - M (Q - 1) + ∑ r ∈ (H Q ℓ).primeFactors, (1 / r : ℝ) := by
  rw [M_pow_sub_one_eq hQ hℓ hnd]
  have h1 := M_H_ge (Q := Q) hℓ
  have h2 := M_le_one (Q - 1)
  have h3 := M_nonneg (Q - 1)
  have h4 : 0 ≤ ∑ r ∈ (H Q ℓ).primeFactors, (1 / r : ℝ) := sum_nonneg (fun r _ => by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h1 h3, mul_le_mul_of_nonneg_right h2 h4]

end ArithDyn
