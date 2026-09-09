import ArithDyn.Density.Count
import ArithDyn.Density.PrimeDegree
import ArithDyn.Density.Factorial

/-!
# Density oscillation of the totally defined locus (paper §4, Theorem 4.2 and Corollary 4.9)

For a family of finite fields `L k` with `#(L k) = Q^k`, the density
`δ_Q(k) = #ℙ²(L k)_f / (Q^{2k} + Q^k + 1)` (4.7) satisfies
`liminf δ_Q(k) = 1 - 𝓜(Q-1)` and `limsup δ_Q(k) = 1` (4.8).
For `Q = 2` the liminf is `0`, which refutes Conjecture 18.10(b) of Benedetto et al.
-/

set_option autoImplicit false

namespace ArithDyn.Density

open Filter Topology Finset

/-- The density value `1 - (𝓐(q-1)+3)/(q²+q+1)` as a function of `q = #𝔽` (cf. (4.20)). -/
noncomputable def δ (q : ℕ) : ℝ := 1 - ((A (q - 1) : ℝ) + 3) / ((q : ℝ) ^ 2 + q + 1)

/-- The actual density of `ℙ²(L)_f` equals `δ (#L)` (Proposition 4.5). -/
theorem density_eq (L : Type*) [Field L] [Fintype L] :
    (Nat.card {P : P2 L // TotallyDefined P} : ℝ) /
      ((Fintype.card L : ℝ) ^ 2 + Fintype.card L + 1) = δ (Fintype.card L) := by
  classical
  have h := card_totallyDefined (K := L)
  have hpos : (0 : ℝ) < (Fintype.card L : ℝ) ^ 2 + Fintype.card L + 1 := by positivity
  rw [δ, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast h

lemma δ_le_one (q : ℕ) : δ q ≤ 1 := by
  unfold δ
  have : 0 ≤ ((A (q - 1) : ℝ) + 3) / ((q : ℝ) ^ 2 + q + 1) := by positivity
  linarith

lemma δ_nonneg {q : ℕ} (hq : 1 ≤ q) : 0 ≤ δ q := by
  unfold δ
  have hD : (0 : ℝ) < (q : ℝ) ^ 2 + q + 1 := by positivity
  rw [sub_nonneg, div_le_one hD]
  have h1 : (A (q - 1) : ℝ) ≤ ((q - 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast A_le_sq (q - 1)
  have h2 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq]; simp
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rw [h2] at h1
  nlinarith

/-- The two-sided bound (4.20)–(4.21): `|δ(n+1) - (1 - 𝓜 n)| ≤ 3/n`. -/
lemma δ_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 - M n - 3 / n ≤ δ (n + 1) ∧ δ (n + 1) ≤ 1 - M n + 3 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : (A n : ℝ) = M n * (n : ℝ) ^ 2 := by unfold M; field_simp
  have hM0 := M_nonneg n
  have hM1 := M_le_one n
  unfold δ
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [hA]
  set x := M n with hx
  set y : ℝ := 1 / n with hy
  have hy0 : 0 < y := by positivity
  have hyn : y * n = 1 := by rw [hy]; field_simp
  have hyn2 : y * (n : ℝ) ^ 2 = n := by rw [pow_two, ← mul_assoc, hyn, one_mul]
  have hD : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 + ((n : ℝ) + 1) + 1 := by positivity
  have hxn : x * n ≤ n := by nlinarith
  have hxn0 : 0 ≤ x * n := mul_nonneg hM0 hn'.le
  have h3 : (3 : ℝ) / n = 3 * y := by rw [hy]; ring
  rw [h3]
  constructor
  · rw [sub_sub, sub_le_sub_iff_left, div_le_iff₀ hD]
    nlinarith [hyn, hyn2, hxn0, hy0, hM0, hn']
  · rw [sub_add, sub_le_sub_iff_left, le_div_iff₀ hD]
    nlinarith [hyn, hyn2, hxn0, hy0, hM0, hn', hxn]

lemma pow_sub_one_ge {Q k : ℕ} (hQ : 2 ≤ Q) : k ≤ Q ^ k - 1 := by
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ k ≤ Q ^ k := Nat.pow_le_pow_left hQ k
  omega

lemma three_div_le {ε : ℝ} (hε : 0 < ε) {k n : ℕ} (hk : ⌈3 / ε⌉₊ + 1 ≤ k) (hkn : k ≤ n) :
    3 / (n : ℝ) ≤ ε := by
  have h1 : (3 / ε : ℝ) ≤ k := by
    have := Nat.le_ceil (3 / ε)
    have h2 : ((⌈3 / ε⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega : ⌈3 / ε⌉₊ ≤ k)
    linarith
  have hk0 : (0 : ℝ) < k := by
    have : (0 : ℝ) < 3 / ε := by positivity
    linarith
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hk0 (by exact_mod_cast hkn)
  rw [div_le_iff₀ hn0]
  have : (3 / ε) * ε ≤ (k : ℝ) * ε := mul_le_mul_of_nonneg_right h1 hε.le
  rw [div_mul_cancel₀ _ hε.ne'] at this
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  nlinarith

/-- (4.22): `δ_Q(k) ≥ 1 - 𝓜(Q-1) - 3/(Q^k-1)` for `k ≥ 1`. -/
lemma δ_pow_ge {Q k : ℕ} (hQ : 2 ≤ Q) (hk : 1 ≤ k) :
    1 - M (Q - 1) - 3 / ((Q ^ k - 1 : ℕ) : ℝ) ≤ δ (Q ^ k) := by
  have hn : 1 ≤ Q ^ k - 1 := by
    have := pow_sub_one_ge (k := k) hQ
    omega
  have h := (δ_bounds hn).1
  rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))] at h
  have hM : M (Q ^ k - 1) ≤ M (Q - 1) := M_le_of_dvd (Nat.sub_one_dvd_pow_sub_one Q k)
  linarith

lemma δ_pow_le {Q k : ℕ} (hQ : 2 ≤ Q) (hk : 1 ≤ k) :
    δ (Q ^ k) ≤ 1 - M (Q ^ k - 1) + 3 / ((Q ^ k - 1 : ℕ) : ℝ) := by
  have hn : 1 ≤ Q ^ k - 1 := by
    have := pow_sub_one_ge (k := k) hQ
    omega
  have h := (δ_bounds hn).2
  rwa [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))] at h

/-- Proposition 4.7, prime degrees: `δ_Q(ℓ) ≤ 1 - 𝓜(Q-1) + ε` for infinitely many `ℓ`. -/
theorem frequently_δ_le {Q : ℕ} (hQ : 2 ≤ Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ k in atTop, δ (Q ^ k) ≤ 1 - M (Q - 1) + ε := by
  rw [frequently_atTop]
  intro N₀
  set K₀ : ℕ := ⌈1 / ε⌉₊ + 1 with hK₀
  have hK₀pos : 1 ≤ K₀ := by omega
  have hK₀ε : 1 / (2 * (K₀ : ℝ)) ≤ ε / 2 := by
    have h1 : (1 / ε : ℝ) ≤ K₀ := by
      have := Nat.le_ceil (1 / ε)
      have h2 : ((⌈1 / ε⌉₊ : ℕ) : ℝ) ≤ K₀ := by exact_mod_cast (by omega : ⌈1 / ε⌉₊ ≤ K₀)
      linarith
    have hK : (0 : ℝ) < K₀ := by exact_mod_cast hK₀pos
    rw [div_le_iff₀ (by positivity)]
    have : (1 / ε) * ε ≤ (K₀ : ℝ) * ε := mul_le_mul_of_nonneg_right h1 hε.le
    rw [div_mul_cancel₀ _ hε.ne'] at this
    nlinarith
  obtain ⟨ℓ, hℓge, hℓp⟩ :=
    Nat.exists_infinite_primes (N₀ + Q ^ K₀ + Q + 3 + (⌈3 / (ε / 2)⌉₊ + 1))
  refine ⟨ℓ, by omega, ?_⟩
  have hodd : Odd ℓ := hℓp.odd_of_ne_two (by omega)
  have hnd : ¬ ℓ ∣ Q - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hK : Q ^ K₀ ≤ 2 * ℓ + 1 := by omega
  have hcard := card_primeFactors_H_le hQ hℓp hodd hnd hK
  have hsum := sum_inv_primeFactors_le hQ hℓp hodd hnd
  have hcd := card_div_le hK₀pos hcard
  have h1 := one_sub_M_le hQ hℓp hnd
  have h2 := δ_pow_le hQ hℓp.one_le
  have h3 : 3 / ((Q ^ ℓ - 1 : ℕ) : ℝ) ≤ ε / 2 :=
    three_div_le (by positivity) (by omega) (pow_sub_one_ge hQ)
  linarith

/-- Proposition 4.8, factorial degrees: `δ_Q(N!) ≥ 1 - ε` for all large `N`. -/
theorem frequently_δ_ge {Q : ℕ} (hQ : 2 ≤ Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ k in atTop, 1 - ε ≤ δ (Q ^ k) := by
  have hfact : Tendsto (fun N : ℕ => N.factorial) atTop atTop :=
    tendsto_atTop_mono Nat.self_le_factorial tendsto_id
  apply hfact.frequently
  apply Eventually.frequently
  have h1 := tendsto_M_factorial Q (by omega)
  have h2 : Tendsto (fun N : ℕ => 3 / ((Q ^ N.factorial - 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat 3) (Eventually.of_forall (fun N => by positivity)) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hle : N ≤ Q ^ N.factorial - 1 := (Nat.self_le_factorial N).trans (pow_sub_one_ge hQ)
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    exact div_le_div_of_nonneg_left (by norm_num) hN' (by exact_mod_cast hle)
  have h3 : ∀ᶠ N : ℕ in atTop,
      1 - M (Q ^ N.factorial - 1) - 3 / ((Q ^ N.factorial - 1 : ℕ) : ℝ) ≤
        δ (Q ^ N.factorial) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : 1 ≤ Q ^ N.factorial - 1 := by
      have := (Nat.self_le_factorial N).trans (pow_sub_one_ge (k := N.factorial) hQ)
      omega
    have h := (δ_bounds hn).1
    rwa [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))] at h
  have h4 : Tendsto
      (fun N : ℕ => 1 - M (Q ^ N.factorial - 1) - 3 / ((Q ^ N.factorial - 1 : ℕ) : ℝ))
      atTop (𝓝 (1 - 0 - 0)) := (tendsto_const_nhds.sub h1).sub h2
  have h5 := (tendsto_order.1 h4).1 (1 - ε) (by linarith)
  filter_upwards [h3, h5] with N hN1 hN2
  linarith

lemma δ_bdd_below {Q : ℕ} (hQ : 2 ≤ Q) :
    IsBoundedUnder (· ≥ ·) atTop (fun k => δ (Q ^ k)) :=
  isBoundedUnder_of ⟨0, fun k => δ_nonneg (Nat.one_le_pow _ _ (by omega))⟩

lemma δ_bdd_above {Q : ℕ} : IsBoundedUnder (· ≤ ·) atTop (fun k => δ (Q ^ k)) :=
  isBoundedUnder_of ⟨1, fun k => δ_le_one _⟩

/-- Proposition 4.7: `liminf δ_Q(k) = 1 - 𝓜(Q-1)`. -/
theorem liminf_δ {Q : ℕ} (hQ : 2 ≤ Q) :
    liminf (fun k => δ (Q ^ k)) atTop = 1 - M (Q - 1) := by
  apply le_antisymm
  · apply liminf_le_of_le (δ_bdd_below hQ)
    intro b hb
    by_contra hlt
    push_neg at hlt
    obtain ⟨k, hk1, hk2⟩ := (hb.and_frequently
      (frequently_δ_le hQ (half_pos (sub_pos.2 hlt)))).exists
    linarith
  · apply le_of_forall_pos_le_add
    intro ε hε
    have h : 1 - M (Q - 1) - ε ≤ liminf (fun k => δ (Q ^ k)) atTop := by
      apply le_liminf_of_le δ_bdd_above.isCoboundedUnder_ge
      filter_upwards [eventually_ge_atTop (⌈3 / ε⌉₊ + 1)] with k hk
      have h1 := δ_pow_ge hQ (by omega : 1 ≤ k)
      have h2 : 3 / ((Q ^ k - 1 : ℕ) : ℝ) ≤ ε := three_div_le hε hk (pow_sub_one_ge hQ)
      linarith
    linarith

/-- Proposition 4.8: `limsup δ_Q(k) = 1`. -/
theorem limsup_δ {Q : ℕ} (hQ : 2 ≤ Q) : limsup (fun k => δ (Q ^ k)) atTop = 1 := by
  apply le_antisymm
  · exact limsup_le_of_le (δ_bdd_below hQ).isCoboundedUnder_le
      (Eventually.of_forall (fun k => δ_le_one _))
  · apply le_limsup_of_le δ_bdd_above
    intro b hb
    by_contra hlt
    push_neg at hlt
    obtain ⟨k, hk1, hk2⟩ := (hb.and_frequently
      (frequently_δ_ge hQ (half_pos (sub_pos.2 hlt)))).exists
    linarith

/-! ### The main theorem for a family of finite fields `L k` with `#(L k) = Q^k` -/

variable (L : ℕ → Type*) [∀ k, Field (L k)] [∀ k, Fintype (L k)]

/-- The density `δ_Q(k) = #ℙ²(L k)_f / (Q^{2k} + Q^k + 1)` of (4.7). -/
noncomputable def densityFamily (Q k : ℕ) : ℝ :=
  (Nat.card {P : P2 (L k) // TotallyDefined P} : ℝ) / ((Q : ℝ) ^ (2 * k) + (Q : ℝ) ^ k + 1)

lemma densityFamily_eq {Q : ℕ} (hL : ∀ k, 1 ≤ k → Fintype.card (L k) = Q ^ k) {k : ℕ}
    (hk : 1 ≤ k) : densityFamily L Q k = δ (Q ^ k) := by
  have hc : (Fintype.card (L k) : ℝ) = (Q : ℝ) ^ k := by exact_mod_cast hL k hk
  rw [densityFamily, ← hL k hk, ← density_eq (L k), hc]
  congr 1
  ring

/-- Theorem 4.2, (4.8), first half: `liminf_k δ_Q(k) = 1 - 𝓜(Q-1)`. -/
theorem liminf_density {Q : ℕ} (hQ : 2 ≤ Q) (hL : ∀ k, 1 ≤ k → Fintype.card (L k) = Q ^ k) :
    liminf (densityFamily L Q) atTop = 1 - M (Q - 1) := by
  rw [← liminf_δ hQ]
  apply liminf_congr
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact densityFamily_eq L hL hk

/-- Theorem 4.2, (4.8), second half: `limsup_k δ_Q(k) = 1`. -/
theorem limsup_density {Q : ℕ} (hQ : 2 ≤ Q) (hL : ∀ k, 1 ≤ k → Fintype.card (L k) = Q ^ k) :
    limsup (densityFamily L Q) atTop = 1 := by
  rw [← limsup_δ hQ]
  apply limsup_congr
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact densityFamily_eq L hL hk

/-- Theorem 4.2: the density does not converge, for any base field size `Q`. -/
theorem density_not_convergent {Q : ℕ} (hQ : 2 ≤ Q)
    (hL : ∀ k, 1 ≤ k → Fintype.card (L k) = Q ^ k) :
    ¬ ∃ c : ℝ, Tendsto (densityFamily L Q) atTop (𝓝 c) := by
  rintro ⟨c, hc⟩
  have h1 := hc.liminf_eq
  have h2 := hc.limsup_eq
  rw [liminf_density L hQ hL] at h1
  rw [limsup_density L hQ hL] at h2
  have := M_pos (n := Q - 1) (by omega)
  linarith

/-- For `Q = 2` the liminf is `0`. -/
theorem liminf_density_two (hL : ∀ k, 1 ≤ k → Fintype.card (L k) = 2 ^ k) :
    liminf (densityFamily L 2) atTop = 0 := by
  rw [liminf_density L le_rfl hL]
  simp

/-- Corollary 4.9: Conjecture 18.10(b) of Benedetto–Ingram–Jones–Manes–Silverman–Tucker fails
for the cubic birational map `f` over `𝔽₂`: the density of `ℙ²(𝔽_{2^k})_f` does not tend to `1`. -/
theorem not_tendsto_one (hL : ∀ k, 1 ≤ k → Fintype.card (L k) = 2 ^ k) :
    ¬ Tendsto (densityFamily L 2) atTop (𝓝 1) := by
  intro h
  have := h.liminf_eq
  rw [liminf_density_two L hL] at this
  norm_num at this

end ArithDyn.Density
