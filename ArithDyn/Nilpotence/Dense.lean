import Mathlib

/-!
# Zariski density of the escaping set `E` (paper §5.4, Lemma 5.7, first part)

`E = {(u,v) : u ≠ 0, 1, v ≠ 0, uⁿ v ≠ 1 ∀ n}` (for `u` of finite order this is `v ∉ ⟨u⟩`, (5.15)).
Over an infinite field in which every nonzero element is a root of unity, every polynomial in
`K[v, u]` vanishing on `E` is zero.

Convention: in `MvPolynomial (Fin 2) K`, `X 0 = v` and `X 1 = u`; a pair `(u, v)` is evaluated as
`eval ![v, u]`.
-/

set_option autoImplicit false

namespace ArithDyn.Nilpotence

open MvPolynomial

variable {K : Type*} [Field K]

/-- The escaping set `E` (5.15). -/
def Eset (K : Type*) [Field K] : Set (K × K) :=
  {p | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ 1 ∧ ∀ n : ℕ, p.1 ^ n * p.2 ≠ 1}

/-- For `u` of finite order, only finitely many `v` satisfy `uⁿ v = 1` for some `n`. -/
lemma finite_bad_v {u : K} {M : ℕ} (hM : 0 < M) (hu : u ^ M = 1) :
    Set.Finite {v : K | ∃ n : ℕ, u ^ n * v = 1} := by
  apply (Set.finite_range (fun n : Fin M => (u ^ (n : ℕ))⁻¹)).subset
  rintro v ⟨n, hn⟩
  refine ⟨⟨n % M, Nat.mod_lt _ hM⟩, ?_⟩
  have hu' : u ^ n = u ^ (n % M) := by
    conv_lhs => rw [← Nat.mod_add_div n M, pow_add, pow_mul, hu, one_pow, mul_one]
  show (u ^ (n % M))⁻¹ = v
  rw [← hu']
  exact (eq_inv_of_mul_eq_one_right hn).symm

/-- Lemma 5.7 (first part): a polynomial vanishing on `E` is zero. -/
theorem eq_zero_of_vanish_on_Eset [Infinite K]
    (hfin : ∀ u : K, u ≠ 0 → ∃ M : ℕ, 0 < M ∧ u ^ M = 1)
    (P : MvPolynomial (Fin 2) K) (hP : ∀ p ∈ Eset K, eval ![p.2, p.1] P = 0) : P = 0 := by
  -- for each `u ≠ 0, 1`, the specialization `Q_u ∈ K[v]` vanishes on a cofinite set
  have hQu : ∀ u : K, u ≠ 0 → u ≠ 1 →
      Polynomial.map (eval (fun _ : Fin 1 => u)) (finSuccEquiv K 1 P) = 0 := by
    intro u hu0 hu1
    obtain ⟨M, hM, huM⟩ := hfin u hu0
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hfin' : Set.Finite ({0} ∪ {v : K | ∃ n : ℕ, u ^ n * v = 1}) :=
      (Set.finite_singleton 0).union (finite_bad_v hM huM)
    apply hfin'.infinite_compl.mono
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, not_or,
      not_exists] at hv
    obtain ⟨hv0, hvn⟩ := hv
    show Polynomial.IsRoot _ v
    rw [Polynomial.IsRoot, ← eval_eq_eval_mv_eval']
    have hmem : (u, v) ∈ Eset K := ⟨hu0, hv0, hu1, hvn⟩
    have := hP (u, v) hmem
    have hvec : (Fin.cons v (fun _ : Fin 1 => u) : Fin 2 → K) = ![v, u] := by
      funext i; fin_cases i <;> rfl
    rw [hvec]
    exact this
  -- hence every coefficient (a polynomial in `u`) vanishes at all `u ≠ 0, 1`, so is zero
  have hcoeff : ∀ i, (finSuccEquiv K 1 P).coeff i = 0 := by
    intro i
    have h1 : ∀ u : K, u ≠ 0 → u ≠ 1 →
        eval (fun _ : Fin 1 => u) ((finSuccEquiv K 1 P).coeff i) = 0 := by
      intro u hu0 hu1
      have := congrArg (fun q => Polynomial.coeff q i) (hQu u hu0 hu1)
      simpa [Polynomial.coeff_map] using this
    have h2 : X 0 * (X 0 - 1) * (finSuccEquiv K 1 P).coeff i = 0 := by
      apply MvPolynomial.funext
      intro x
      simp only [map_mul, map_sub, eval_X, map_one, map_zero]
      by_cases hx0 : x 0 = 0
      · simp [hx0]
      by_cases hx1 : x 0 = 1
      · simp [hx1]
      have hx : (fun _ : Fin 1 => x 0) = x := by funext j; fin_cases j; rfl
      have := h1 (x 0) hx0 hx1
      rw [hx] at this
      rw [this, mul_zero]
    have h3 : X 0 * (X 0 - 1) ≠ (0 : MvPolynomial (Fin 1) K) := by
      apply mul_ne_zero (X_ne_zero 0)
      intro h
      have := congrArg (eval (fun _ => (0 : K))) h
      simp at this
    exact (mul_eq_zero.1 h2).resolve_left h3
  have hQ0 : finSuccEquiv K 1 P = 0 :=
    Polynomial.ext (fun i => by rw [hcoeff i, Polynomial.coeff_zero])
  have := congrArg (finSuccEquiv K 1).symm hQ0
  simpa using this

/-- Contrapositive form used in the elimination argument. -/
theorem exists_Eset_eval_ne_zero [Infinite K]
    (hfin : ∀ u : K, u ≠ 0 → ∃ M : ℕ, 0 < M ∧ u ^ M = 1)
    {P : MvPolynomial (Fin 2) K} (hP : P ≠ 0) : ∃ p ∈ Eset K, eval ![p.2, p.1] P ≠ 0 := by
  by_contra h
  push_neg at h
  exact hP (eq_zero_of_vanish_on_Eset hfin P h)

end ArithDyn.Nilpotence
