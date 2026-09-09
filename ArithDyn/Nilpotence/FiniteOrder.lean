import Mathlib

/-!
# Finite multiplicative order in fields algebraic over `𝔽_p`

Every nonzero element of a field algebraic over `ZMod p` (e.g. `AlgebraicClosure (ZMod p)`)
has finite multiplicative order coprime to `p`. This is the arithmetic input of §5.
-/

set_option autoImplicit false

namespace ArithDyn.Nilpotence

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]
  [Algebra.IsAlgebraic (ZMod p) K]

/-- In a field algebraic over `𝔽_p`, every nonzero element `t` satisfies `t^M = 1` for some
`M > 0` coprime to `p`. -/
theorem exists_pow_eq_one_coprime (t : K) (ht : t ≠ 0) :
    ∃ M : ℕ, 0 < M ∧ Nat.Coprime M p ∧ t ^ M = 1 := by
  let F := IntermediateField.adjoin (ZMod p) ({t} : Set K)
  haveI : FiniteDimensional (ZMod p) F :=
    IntermediateField.adjoin.finiteDimensional
      ((Algebra.IsAlgebraic.isAlgebraic (R := ZMod p) t).isIntegral)
  haveI : Finite F := Module.finite_of_finite (ZMod p)
  letI : Fintype F := Fintype.ofFinite F
  have htF : t ∈ F := IntermediateField.mem_adjoin_simple_self (ZMod p) t
  set tF : F := ⟨t, htF⟩ with htF_def
  have hcard : Fintype.card F = p ^ Module.finrank (ZMod p) F := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := F), ZMod.card]
  have hrank : 1 ≤ Module.finrank (ZMod p) F := Module.finrank_pos
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  refine ⟨Fintype.card F - 1, by omega, ?_, ?_⟩
  · -- `gcd (p^n - 1, p) = 1`
    have hnd : ¬ p ∣ Fintype.card F - 1 := by
      intro hdvd
      have hpc : p ∣ Fintype.card F := by
        rw [hcard]; exact dvd_pow_self p (by omega)
      have : p ∣ Fintype.card F - (Fintype.card F - 1) := Nat.dvd_sub hpc hdvd
      rw [Nat.sub_sub_self (by omega)] at this
      exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)
    exact ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hnd).symm
  · have hne : tF ≠ 0 := by
      intro h; apply ht
      have := congrArg Subtype.val h
      simpa [htF_def] using this
    have := FiniteField.pow_card_sub_one_eq_one tF hne
    have := congrArg Subtype.val this
    simpa [htF_def] using this

/-- Shifted exponent: if `t^M = 1` with `gcd(q, M) = 1`, then `t^(1 + n q) = 1` for some `n`. -/
theorem exists_pow_shift_eq_one {t : K} {M q : ℕ} (hM : 0 < M) (ht : t ^ M = 1)
    (hcop : Nat.Coprime q M) : ∃ n : ℕ, t ^ (1 + n * q) = 1 := by
  rcases Nat.lt_or_ge 1 M with hM1 | hM1
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hM1
    refine ⟨m * (M - 1), ?_⟩
    have hmod : (q * m) % M = 1 % M := by rw [hm, Nat.mod_eq_of_lt hM1]
    have h1 : 1 + m * (M - 1) * q ≡ 1 + 1 * (M - 1) [MOD M] := by
      have : 1 + m * (M - 1) * q = 1 + (q * m) * (M - 1) := by ring
      rw [this]
      exact Nat.ModEq.add_left 1 (Nat.ModEq.mul_right (M - 1) hmod)
    have h2 : 1 + 1 * (M - 1) = M := by omega
    rw [h2] at h1
    have h3 : M ∣ 1 + m * (M - 1) * q := (Nat.modEq_zero_iff_dvd).1 (h1.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))
    obtain ⟨c, hc⟩ := h3
    rw [hc, pow_mul, ht, one_pow]
  · have hM' : M = 1 := by omega
    subst hM'
    refine ⟨0, ?_⟩
    simpa using ht

theorem exists_pow_shift_eq_one' (t : K) (ht : t ≠ 0) (s : ℕ) :
    ∃ n : ℕ, t ^ (1 + n * p ^ s) = 1 := by
  obtain ⟨M, hM, hcop, htM⟩ := exists_pow_eq_one_coprime (p := p) t ht
  exact exists_pow_shift_eq_one hM htM (Nat.Coprime.pow_left s hcop.symm)

end ArithDyn.Nilpotence

namespace ArithDyn.Nilpotence

/-- The hypothesis used in the geometric part of §5: every nonzero element is a root of unity. -/
theorem forall_exists_pow_eq_one (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]
    [Algebra.IsAlgebraic (ZMod p) K] (u : K) (hu : u ≠ 0) : ∃ M : ℕ, 0 < M ∧ u ^ M = 1 := by
  obtain ⟨M, hM, -, hu⟩ := exists_pow_eq_one_coprime (p := p) u hu
  exact ⟨M, hM, hu⟩

end ArithDyn.Nilpotence
