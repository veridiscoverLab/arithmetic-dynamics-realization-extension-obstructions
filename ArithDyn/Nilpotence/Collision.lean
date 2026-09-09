import Mathlib

/-!
# Monomial re-exponentiation and the exponent-collision lemma (paper §5.5, replacing Lemma 5.10)

For `d ∈ K[v,u]` (`X 0 = v`, `X 1 = u`) with support `S` and total degree `D`, we form
* `subst3 d ex ey ez = ∑_{s ∈ S} c_s x^{ex s} y^{ey s} z^{ez s} ∈ K[x,y,z]`,
* `ppoly d e = ∑_{s ∈ S} c_s X^{e s} ∈ K[X]`.

If `e` is injective on `S` and `d ≠ 0` then `ppoly d e ≠ 0`. The exponent map
`ℓ(s) = q (s 1 + m (D - s 0) + k s 0) + s 0` is injective on `S` as soon as `q > D`, because
`s 0 = ℓ(s) mod q`.
-/

set_option autoImplicit false

namespace ArithDyn.Nilpotence

open MvPolynomial Finset

variable {K : Type*} [Field K]

/-- `∑_{s ∈ supp d} c_s X^{e s}`. -/
noncomputable def ppoly (d : MvPolynomial (Fin 2) K) (e : (Fin 2 →₀ ℕ) → ℕ) : Polynomial K :=
  ∑ s ∈ d.support, Polynomial.C (coeff s d) * Polynomial.X ^ (e s)

lemma ppoly_eval (d : MvPolynomial (Fin 2) K) (e : (Fin 2 →₀ ℕ) → ℕ) (t : K) :
    (ppoly d e).eval t = ∑ s ∈ d.support, coeff s d * t ^ (e s) := by
  simp [ppoly, Polynomial.eval_finset_sum]

lemma ppoly_ne_zero (d : MvPolynomial (Fin 2) K) (e : (Fin 2 →₀ ℕ) → ℕ) (hd : d ≠ 0)
    (hinj : Set.InjOn e d.support) : ppoly d e ≠ 0 := by
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ d.support :=
    Finset.nonempty_iff_ne_empty.2 (fun h => hd (support_eq_empty.1 h))
  intro h
  have := congrArg (fun q => Polynomial.coeff q (e s₀)) h
  simp only [ppoly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single s₀] at this
  · simp only [if_true] at this
    exact (mem_support_iff.1 hs₀) this
  · intro s hs hne
    rw [if_neg]
    intro heq
    exact hne (hinj hs hs₀ heq.symm)
  · intro h'; exact absurd hs₀ h'

/-- `∑_{s ∈ supp d} c_s X0^{ex s} X1^{ey s} X2^{ez s}`. -/
noncomputable def subst3 (d : MvPolynomial (Fin 2) K) (ex ey ez : (Fin 2 →₀ ℕ) → ℕ) :
    MvPolynomial (Fin 3) K :=
  ∑ s ∈ d.support, monomial (Finsupp.single 0 (ex s) + Finsupp.single 1 (ey s) +
    Finsupp.single 2 (ez s)) (coeff s d)

lemma eval_subst3 (d : MvPolynomial (Fin 2) K) (ex ey ez : (Fin 2 →₀ ℕ) → ℕ) (a : Fin 3 → K) :
    eval a (subst3 d ex ey ez) =
      ∑ s ∈ d.support, coeff s d * (a 0 ^ ex s * a 1 ^ ey s * a 2 ^ ez s) := by
  simp only [subst3, map_sum, eval_monomial]
  refine sum_congr rfl (fun s _ => ?_)
  congr 1
  rw [Finsupp.prod_add_index' (fun i => pow_zero _) (fun i m n => pow_add _ _ _),
    Finsupp.prod_add_index' (fun i => pow_zero _) (fun i m n => pow_add _ _ _)]
  simp [Finsupp.prod_single_index]

lemma eval_two (d : MvPolynomial (Fin 2) K) (v u : K) :
    eval ![v, u] d = ∑ s ∈ d.support, coeff s d * (v ^ s 0 * u ^ s 1) := by
  rw [eval_eq']
  refine sum_congr rfl (fun s _ => ?_)
  rw [Fin.prod_univ_two]
  simp

lemma support_le_totalDegree {d : MvPolynomial (Fin 2) K} {s : Fin 2 →₀ ℕ} (hs : s ∈ d.support) :
    s 0 + s 1 ≤ d.totalDegree := by
  have := le_totalDegree hs
  rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this

/-- The per-monomial exponent identity behind (5.17)–(5.18). -/
lemma monomial_identity (u w z : K) {α β D m : ℕ} (hβ : β ≤ D) (hαβ : α + β ≤ D) :
    (u * z) ^ (α + m * (D - β)) * (w * z) ^ β * z ^ (D - α - β + β * m) =
      u ^ (α + m * (D - β)) * w ^ β * z ^ ((m + 1) * D) := by
  obtain ⟨D₁, rfl⟩ := Nat.exists_eq_add_of_le hαβ
  have e1 : α + β + D₁ - β = α + D₁ := by omega
  have e2 : α + β + D₁ - α - β = D₁ := by omega
  rw [e1, e2]
  ring

/-- The exponent map `ℓ` is injective on the support when `q > D`. -/
lemma ell_injOn (d : MvPolynomial (Fin 2) K) {q m k : ℕ} (hq : d.totalDegree < q) :
    Set.InjOn (fun s : Fin 2 →₀ ℕ => q * (s 1 + m * (d.totalDegree - s 0) + k * s 0) + s 0)
      d.support := by
  intro s hs s' hs' h
  simp only at h
  have hs0 : s 0 < q := lt_of_le_of_lt (by have := support_le_totalDegree hs; omega) hq
  have hs0' : s' 0 < q := lt_of_le_of_lt (by have := support_le_totalDegree hs'; omega) hq
  have hq0 : 0 < q := by omega
  have h0 : s 0 = s' 0 := by
    have h1 := congrArg (· % q) h
    simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hs0, Nat.mod_eq_of_lt hs0'] at h1
    exact h1
  have h1 : s 1 = s' 1 := by
    rw [h0] at h
    have := Nat.eq_of_mul_eq_mul_left hq0 (Nat.add_right_cancel h)
    omega
  ext i
  fin_cases i
  · exact h0
  · exact h1

end ArithDyn.Nilpotence
