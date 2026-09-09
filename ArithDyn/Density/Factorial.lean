import ArithDyn.Density.MeanOrder

/-!
# Factorial extension degrees (paper §4.3, proof of Proposition 4.8, (4.27)–(4.31))

For `N → ∞`, `𝓜(Q^{N!} - 1) → 0`: every prime `r ≤ N+1` with `r ∤ Q` divides `Q^{N!} - 1`
(Fermat), so `𝓜(Q^{N!}-1) ≤ ∏ 𝓜(r) ≤ ∏ (1 - 1/(2r)) ≤ exp(-½ ∑ 1/r)`, and `∑_{r ≤ x} 1/r → ∞`
(Mathlib: `not_summable_one_div_on_primes`).
-/

set_option autoImplicit false

namespace ArithDyn

open Finset Filter Topology

/-- The primes `r ≤ N + 1` not dividing `Q`. -/
def Sset (Q N : ℕ) : Finset ℕ := ((range (N + 2)).filter Nat.Prime).filter (fun r => ¬ r ∣ Q)

lemma mem_Sset {Q N r : ℕ} : r ∈ Sset Q N ↔ r < N + 2 ∧ r.Prime ∧ ¬ r ∣ Q := by
  simp [Sset, and_assoc]

lemma dvd_of_mem_Sset {Q N r : ℕ} (hQ : 1 ≤ Q) (hr : r ∈ Sset Q N) :
    r ∣ Q ^ N.factorial - 1 := by
  obtain ⟨hlt, hp, hnd⟩ := mem_Sset.1 hr
  haveI := Fact.mk hp
  have hQ0 : (Q : ZMod r) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hnd
  have h1 : (Q : ZMod r) ^ (r - 1) = 1 := ZMod.pow_card_sub_one_eq_one hQ0
  have h2 : r - 1 ∣ N.factorial :=
    Nat.dvd_factorial (by have := hp.two_le; omega) (by omega)
  obtain ⟨t, ht⟩ := h2
  have h3 : (Q : ZMod r) ^ N.factorial = 1 := by rw [ht, pow_mul, h1, one_pow]
  have h4 : ((Q ^ N.factorial - 1 : ℕ) : ZMod r) = 0 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hQ), Nat.cast_pow, Nat.cast_one, h3, sub_self]
  exact (ZMod.natCast_eq_zero_iff _ _).1 h4

lemma prod_Sset_dvd {Q N : ℕ} (hQ : 1 ≤ Q) : ∏ r ∈ Sset Q N, r ∣ Q ^ N.factorial - 1 :=
  Finset.prod_primes_dvd _ (fun r hr => Nat.prime_iff.1 (mem_Sset.1 hr).2.1)
    (fun r hr => dvd_of_mem_Sset hQ hr)

lemma M_prod_Sset (Q N : ℕ) : M (∏ r ∈ Sset Q N, r) = ∏ r ∈ Sset Q N, M r := by
  apply M_prod
  intro a ha b hb hab
  exact (Nat.coprime_primes (mem_Sset.1 ha).2.1 (mem_Sset.1 hb).2.1).2 hab

/-- (4.27) sharpened with `𝓜(r) ≤ 1 - 1/(2r) ≤ exp(-1/(2r))`. -/
lemma M_factorial_le (Q N : ℕ) (hQ : 1 ≤ Q) :
    M (Q ^ N.factorial - 1) ≤ Real.exp (-(1 / 2 : ℝ) * ∑ r ∈ Sset Q N, (1 / r : ℝ)) := by
  calc M (Q ^ N.factorial - 1) ≤ M (∏ r ∈ Sset Q N, r) := M_le_of_dvd (prod_Sset_dvd hQ)
    _ = ∏ r ∈ Sset Q N, M r := M_prod_Sset Q N
    _ ≤ ∏ r ∈ Sset Q N, Real.exp (-(1 / 2 : ℝ) * (1 / r)) := by
        apply prod_le_prod (fun r _ => M_nonneg r)
        intro r hr
        have hp := (mem_Sset.1 hr).2.1
        calc M r ≤ 1 - 1 / (2 * (r : ℝ)) := M_prime_le hp
          _ = -(1 / 2 : ℝ) * (1 / r) + 1 := by ring
          _ ≤ Real.exp (-(1 / 2 : ℝ) * (1 / r)) := Real.add_one_le_exp _
    _ = Real.exp (-(1 / 2 : ℝ) * ∑ r ∈ Sset Q N, (1 / r : ℝ)) := by
        rw [mul_sum, Real.exp_sum]

/-- Divergence of `∑_{p ≤ x} 1/p` (from Mathlib's `not_summable_one_div_on_primes`). -/
lemma tendsto_sum_primes :
    Tendsto (fun n : ℕ => ∑ i ∈ (range n).filter Nat.Prime, (1 / i : ℝ)) atTop atTop := by
  have h := not_summable_one_div_on_primes
  rw [summable_iff_not_tendsto_nat_atTop_of_nonneg
    (fun n => Set.indicator_nonneg (fun _ _ => by positivity) _), not_not] at h
  refine h.congr (fun n => ?_)
  rw [sum_filter]
  refine sum_congr rfl (fun i _ => ?_)
  simp [Set.indicator_apply]

lemma sum_Sset_ge (Q N : ℕ) (hQ : 1 ≤ Q) :
    ∑ i ∈ (range (N + 2)).filter Nat.Prime, (1 / i : ℝ) - Q ≤ ∑ r ∈ Sset Q N, (1 / r : ℝ) := by
  have hsplit := sum_filter_add_sum_filter_not ((range (N + 2)).filter Nat.Prime)
    (fun r => ¬ r ∣ Q) (fun r => (1 / r : ℝ))
  have hbound : ∑ r ∈ ((range (N + 2)).filter Nat.Prime).filter (fun r => ¬ ¬ r ∣ Q),
      (1 / r : ℝ) ≤ Q := by
    calc ∑ r ∈ ((range (N + 2)).filter Nat.Prime).filter (fun r => ¬ ¬ r ∣ Q), (1 / r : ℝ)
        ≤ ∑ r ∈ ((range (N + 2)).filter Nat.Prime).filter (fun r => ¬ ¬ r ∣ Q), (1 : ℝ) :=
          sum_le_sum (fun r hr => by
            have h1 : (1 : ℝ) ≤ r := by
              exact_mod_cast (mem_filter.1 (mem_filter.1 hr).1).2.one_le
            exact (div_le_one (by positivity)).2 h1)
      _ = ((((range (N + 2)).filter Nat.Prime).filter (fun r => ¬ ¬ r ∣ Q)).card : ℝ) := by simp
      _ ≤ (Q.divisors.card : ℝ) := by
          norm_cast
          apply card_le_card
          intro r hr
          simp only [mem_filter, not_not] at hr
          exact Nat.mem_divisors.2 ⟨hr.2, by omega⟩
      _ ≤ Q := by exact_mod_cast Nat.card_divisors_le_self Q
  unfold Sset
  linarith

lemma tendsto_sum_Sset (Q : ℕ) (hQ : 1 ≤ Q) :
    Tendsto (fun N => ∑ r ∈ Sset Q N, (1 / r : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun N => ∑ i ∈ (range (N + 2)).filter Nat.Prime, (1 / i : ℝ) - Q)
      atTop atTop := by
    have := tendsto_atTop_add_const_right atTop (-(Q : ℝ))
      (tendsto_sum_primes.comp (tendsto_add_atTop_nat 2))
    simpa [sub_eq_add_neg] using this
  exact tendsto_atTop_mono (fun N => sum_Sset_ge Q N hQ) h1

/-- `𝓜(Q^{N!} - 1) → 0` as `N → ∞`. -/
theorem tendsto_M_factorial (Q : ℕ) (hQ : 1 ≤ Q) :
    Tendsto (fun N : ℕ => M (Q ^ N.factorial - 1)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N => Real.exp (-(1 / 2 : ℝ) * ∑ r ∈ Sset Q N, (1 / r : ℝ)))
      atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have := (tendsto_sum_Sset Q hQ).const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    have h := tendsto_neg_atTop_atBot.comp this
    refine h.congr (fun N => ?_)
    simp [neg_mul]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun N => M_nonneg _)
    (fun N => M_factorial_le Q N hQ)

end ArithDyn
