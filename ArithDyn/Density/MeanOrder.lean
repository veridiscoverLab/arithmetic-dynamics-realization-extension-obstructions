import Mathlib

/-!
# The mean–order functions `𝓐` and `𝓜` (paper §4, (4.4) and Lemma 4.6)

`𝓐 n = ∑_{d ∣ n} d φ(d)` and `𝓜 n = 𝓐 n / n²`.

We prove: multiplicativity, the prime–power formula `(r+1) 𝓐(rᵉ) = r^{2e+1} + 1`,
the divisibility monotonicity `m ∣ n → 𝓜 n ≤ 𝓜 m` (4.18), the bounds
`φ(n)/n ≤ 𝓜 n ≤ 1` (4.19), and the interpretation of `𝓐 n` as the sum of the
orders of the elements of a cyclic group of order `n`.
-/

set_option autoImplicit false

namespace ArithDyn

open Finset ArithmeticFunction Function

/-- `𝓐 n = ∑_{d ∣ n} d * φ d` (4.4). -/
def A (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d * Nat.totient d

/-- The arithmetic function `d ↦ d * φ d`. -/
def dphi : ArithmeticFunction ℕ := ⟨fun d => d * Nat.totient d, by simp⟩

lemma dphi_apply (d : ℕ) : dphi d = d * Nat.totient d := rfl

lemma isMultiplicative_dphi : IsMultiplicative dphi := by
  refine ⟨by simp [dphi_apply], ?_⟩
  intro m n hmn
  simp only [dphi_apply, Nat.totient_mul hmn]
  ring

/-- `𝓐` as an arithmetic function: the Dirichlet convolution `ζ * dphi`. -/
def Afun : ArithmeticFunction ℕ := zeta * dphi

lemma Afun_apply (n : ℕ) : Afun n = A n := by
  rw [Afun, zeta_mul_apply]
  simp [A, dphi_apply]

lemma isMultiplicative_Afun : IsMultiplicative Afun := by
  unfold Afun
  exact isMultiplicative_zeta.mul isMultiplicative_dphi

lemma A_mul {m n : ℕ} (h : Nat.Coprime m n) : A (m * n) = A m * A n := by
  rw [← Afun_apply, ← Afun_apply, ← Afun_apply]
  exact isMultiplicative_Afun.map_mul_of_coprime h

@[simp] lemma A_zero : A 0 = 0 := by simp [A]

@[simp] lemma A_one : A 1 = 1 := by simp [A]

lemma A_prod {ι : Type*} (s : Finset ι) (g : ι → ℕ)
    (hs : (s : Set ι).Pairwise (Nat.Coprime on g)) :
    A (∏ i ∈ s, g i) = ∏ i ∈ s, A (g i) := by
  rw [← Afun_apply, isMultiplicative_Afun.map_prod g s hs]
  simp only [Afun_apply]

/-! ### Elementary bounds -/

lemma A_ge_self (n : ℕ) : n ≤ A n := by
  calc n = ∑ d ∈ n.divisors, Nat.totient d := (Nat.sum_totient n).symm
    _ ≤ ∑ d ∈ n.divisors, d * Nat.totient d :=
        sum_le_sum fun d hd => Nat.le_mul_of_pos_left _ (Nat.pos_of_mem_divisors hd)

lemma A_pos {n : ℕ} (hn : 0 < n) : 0 < A n := lt_of_lt_of_le hn (A_ge_self n)

lemma A_le_sq (n : ℕ) : A n ≤ n ^ 2 := by
  calc A n = ∑ d ∈ n.divisors, d * Nat.totient d := rfl
    _ ≤ ∑ d ∈ n.divisors, n * Nat.totient d :=
        sum_le_sum fun d hd => Nat.mul_le_mul_right _ (Nat.divisor_le hd)
    _ = n * n := by rw [← mul_sum, Nat.sum_totient]
    _ = n ^ 2 := (sq n).symm

lemma mul_totient_le_A {n : ℕ} (hn : 0 < n) : n * Nat.totient n ≤ A n :=
  single_le_sum (f := fun d => d * Nat.totient d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n hn.ne')

/-! ### Prime powers -/

lemma A_prime_pow_sum {r : ℕ} (hr : r.Prime) (e : ℕ) :
    A (r ^ e) = ∑ j ∈ range (e + 1), r ^ j * Nat.totient (r ^ j) := by
  rw [A, Nat.divisors_prime_pow hr, sum_map]
  rfl

lemma A_prime_pow_succ {r : ℕ} (hr : r.Prime) (e : ℕ) :
    A (r ^ (e + 1)) = A (r ^ e) + r ^ (e + 1) * (r ^ e * (r - 1)) := by
  rw [A_prime_pow_sum hr (e + 1), sum_range_succ, ← A_prime_pow_sum hr e,
    Nat.totient_prime_pow hr (Nat.succ_pos e)]
  simp

lemma A_prime_pow_formula {r : ℕ} (hr : r.Prime) (e : ℕ) :
    (r + 1) * A (r ^ e) = r ^ (2 * e + 1) + 1 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [A_prime_pow_succ hr, mul_add, ih]
    have h1 := hr.one_le
    zify [h1] <;> ring

lemma A_prime {r : ℕ} (hr : r.Prime) : A r = 1 + r * (r - 1) := by
  rw [A, hr.divisors, sum_pair hr.one_lt.ne, Nat.totient_one, Nat.totient_prime hr]

/-! ### The real-valued function `𝓜` -/

/-- `𝓜 n = 𝓐 n / n²` (4.4), as a real number. -/
noncomputable def M (n : ℕ) : ℝ := (A n : ℝ) / (n : ℝ) ^ 2

@[simp] lemma M_zero : M 0 = 0 := by simp [M]

@[simp] lemma M_one : M 1 = 1 := by simp [M]

lemma M_nonneg (n : ℕ) : 0 ≤ M n := by unfold M; positivity

lemma M_pos {n : ℕ} (hn : 0 < n) : 0 < M n := by
  unfold M
  have hA : (0 : ℝ) < A n := by exact_mod_cast A_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

lemma M_le_one (n : ℕ) : M n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [M, div_le_one (by positivity)]
    exact_mod_cast A_le_sq n

lemma totient_div_le_M {n : ℕ} (hn : 0 < n) : (Nat.totient n : ℝ) / n ≤ M n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mul_totient_le_A hn
  have h' : ((n * Nat.totient n : ℕ) : ℝ) ≤ (A n : ℝ) := by exact_mod_cast h
  unfold M
  rw [div_le_div_iff₀ hn' (by positivity)]
  push_cast at h' ⊢
  nlinarith [h', hn']

lemma M_mul {m n : ℕ} (h : Nat.Coprime m n) : M (m * n) = M m * M n := by
  unfold M
  rw [A_mul h]
  push_cast
  ring

lemma M_prod {ι : Type*} (s : Finset ι) (g : ι → ℕ)
    (hs : (s : Set ι).Pairwise (Nat.Coprime on g)) :
    M (∏ i ∈ s, g i) = ∏ i ∈ s, M (g i) := by
  unfold M
  rw [A_prod s g hs]
  push_cast
  rw [prod_div_distrib, ← prod_pow]

lemma M_prime_pow {r : ℕ} (hr : r.Prime) (e : ℕ) :
    M (r ^ e) = ((r : ℝ) ^ (2 * e + 1) + 1) / (((r : ℝ) + 1) * (r : ℝ) ^ (2 * e)) := by
  have h := A_prime_pow_formula hr e
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have h' : ((r : ℝ) + 1) * (A (r ^ e) : ℝ) = (r : ℝ) ^ (2 * e + 1) + 1 := by exact_mod_cast h
  have hre : (0 : ℝ) < ((r ^ e : ℕ) : ℝ) := by exact_mod_cast pow_pos hr.pos e
  unfold M
  rw [div_eq_div_iff (by positivity) (by positivity)]
  push_cast
  rw [← h']
  ring

lemma M_prime_pow_succ_le {r : ℕ} (hr : r.Prime) (e : ℕ) : M (r ^ (e + 1)) ≤ M (r ^ e) := by
  rw [M_prime_pow hr, M_prime_pow hr]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr.one_le
  have hx : (0 : ℝ) < (r : ℝ) ^ (2 * e) := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : (r : ℝ) ^ (2 * (e + 1) + 1) = (r : ℝ) ^ (2 * e) * r ^ 3 := by ring
  have e2 : (r : ℝ) ^ (2 * (e + 1)) = (r : ℝ) ^ (2 * e) * r ^ 2 := by ring
  have e3 : (r : ℝ) ^ (2 * e + 1) = (r : ℝ) ^ (2 * e) * r := by ring
  rw [e1, e2, e3]
  have hr2 : (0 : ℝ) ≤ (r : ℝ) ^ 2 - 1 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r + 1) hx.le) hr2]

lemma M_prime {r : ℕ} (hr : r.Prime) : M r = 1 - 1 / (r : ℝ) + 1 / (r : ℝ) ^ 2 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have h : (A r : ℝ) = 1 + (r : ℝ) * ((r : ℝ) - 1) := by
    rw [A_prime hr]
    push_cast [hr.one_le]
    ring
  unfold M
  rw [h]
  field_simp
  ring

lemma M_prime_le {r : ℕ} (hr : r.Prime) : M r ≤ 1 - 1 / (2 * (r : ℝ)) := by
  rw [M_prime hr]
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr.two_le
  have hr0 : (0 : ℝ) < r := by linarith
  have key : 1 / (r : ℝ) ^ 2 ≤ 1 / (2 * (r : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h1 : 1 / (r : ℝ) = 2 * (1 / (2 * (r : ℝ))) := by field_simp
  linarith

/-! ### Divisibility monotonicity (4.18) -/

lemma M_mul_prime_le (m : ℕ) {r : ℕ} (hr : r.Prime) : M (m * r) ≤ M m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [M_nonneg]
  obtain ⟨e, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' r hr.ne_one
  have hcop : Nat.Coprime (r ^ e) m' :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hr).2 hm')
  have hcop' : Nat.Coprime (r ^ (e + 1)) m' :=
    Nat.Coprime.pow_left (e + 1) ((Nat.Prime.coprime_iff_not_dvd hr).2 hm')
  have : r ^ e * m' * r = r ^ (e + 1) * m' := by ring
  rw [this, M_mul hcop', M_mul hcop]
  exact mul_le_mul_of_nonneg_right (M_prime_pow_succ_le hr e) (M_nonneg m')

lemma M_mul_le (m k : ℕ) : M (m * k) ≤ M m := by
  induction k using Nat.recOnMul generalizing m with
  | zero => simp [M_nonneg]
  | one => simp
  | prime p hp => exact M_mul_prime_le m hp
  | mul a b ha hb =>
    calc M (m * (a * b)) = M ((m * a) * b) := by rw [mul_assoc]
      _ ≤ M (m * a) := hb (m * a)
      _ ≤ M m := ha m

/-- (4.18): `m ∣ n → 𝓜 n ≤ 𝓜 m`. -/
lemma M_le_of_dvd {m n : ℕ} (h : m ∣ n) : M n ≤ M m := by
  obtain ⟨k, rfl⟩ := h
  exact M_mul_le m k

/-! ### `𝓐 n` is the sum of the element orders of a cyclic group of order `n` -/

lemma sum_orderOf_eq_A (G : Type*) [Group G] [Fintype G] [IsCyclic G] :
    ∑ g : G, orderOf g = A (Fintype.card G) := by
  classical
  have hmaps : ∀ g ∈ (univ : Finset G), orderOf g ∈ (Fintype.card G).divisors := fun g _ =>
    Nat.mem_divisors.2 ⟨orderOf_dvd_card, Fintype.card_ne_zero⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  unfold A
  refine sum_congr rfl fun d hd => ?_
  rw [sum_congr rfl (fun g hg => (mem_filter.1 hg).2), sum_const, smul_eq_mul, mul_comm,
    IsCyclic.card_orderOf_eq_totient (Nat.dvd_of_mem_divisors hd)]

end ArithDyn
