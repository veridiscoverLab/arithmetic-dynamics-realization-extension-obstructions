import ArithDyn.Nilpotence.Map

/-!
# The curves `Sʲ(C_s)` are pairwise distinct (paper §5.5, Lemma 5.10)

`Sʲ(C_s) = {(u,v) ∈ 𝔾ₘ² : v^{q_s} = u^{1 + j q_s}}` (5.16). Over an infinite field,
`Sʲ(C_s) = Sʰ(C_t)` forces `s = t` and `j = h`.
-/

set_option autoImplicit false

namespace ArithDyn.Nilpotence

variable {K : Type*} [Field K]

/-- The curve `Sʲ(C_s) = {v^q = u^{1 + j q}}` in the torus `(Kˣ)²` (5.16), `q = q_s`. -/
def curveSet (q : ℕ) (j : ℤ) : Set (Kˣ × Kˣ) := {p | p.2 ^ q = p.1 ^ (1 + j * q)}

lemma param_mem_curveSet (q : ℕ) (j : ℤ) (a : Kˣ) :
    (a ^ (q : ℤ), a ^ (1 + j * q)) ∈ curveSet q j := by
  simp only [curveSet, Set.mem_setOf_eq]
  rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

/-- Over an infinite field, distinct integer powers are distinct as functions on `Kˣ`. -/
lemma zpow_injective_of_infinite [Infinite K] {m n : ℤ} (h : ∀ a : Kˣ, a ^ m = a ^ n) : m = n := by
  by_contra hne
  have hk : ∀ a : Kˣ, a ^ (m - n) = 1 := fun a => by rw [zpow_sub, h a]; simp
  -- all nonzero elements are roots of `X^|m-n| - 1`
  have hfin : Set.Finite {x : K | x ^ (m - n).natAbs = 1} := by
    apply (Polynomial.finite_setOf_isRoot
      (Polynomial.X_pow_sub_C_ne_zero (Int.natAbs_pos.2 (sub_ne_zero.2 hne)) (1 : K))).subset
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    simp [Polynomial.IsRoot, hx]
  have hinf : Set.Infinite {x : K | x ≠ 0} := (Set.finite_singleton (0 : K)).infinite_compl
  apply hinf
  apply hfin.subset
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  have h1 := hk (Units.mk0 x hx)
  rcases Int.natAbs_eq (m - n) with h2 | h2
  · rw [h2, zpow_natCast] at h1
    simpa using congrArg Units.val h1
  · rw [h2, zpow_neg, zpow_natCast, inv_eq_one] at h1
    simpa using congrArg Units.val h1

/-- Lemma 5.10: `Sʲ(C_s) = Sʰ(C_t)` implies `s = t` and `j = h`. -/
theorem curveSet_injective [Infinite K] {p : ℕ} (hp : 2 ≤ p) {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    {j h : ℤ} (heq : curveSet (K := K) (p ^ s) j = curveSet (p ^ t) h) : s = t ∧ j = h := by
  have hqs : 2 ≤ p ^ s := le_trans hp (Nat.le_self_pow (by omega) p)
  have hqt : 2 ≤ p ^ t := le_trans hp (Nat.le_self_pow (by omega) p)
  -- the parametrisation of the left curve lies on the right curve
  have hmem : ∀ a : Kˣ, (a ^ ((p ^ s : ℕ) : ℤ), a ^ (1 + j * (p ^ s : ℕ))) ∈ curveSet (p ^ t) h :=
    fun a => heq ▸ param_mem_curveSet (p ^ s) j a
  have hexp : ∀ a : Kˣ, a ^ ((1 + j * (p ^ s : ℕ)) * (p ^ t : ℕ)) =
      a ^ (((p ^ s : ℕ) : ℤ) * (1 + h * (p ^ t : ℕ))) := by
    intro a
    have := hmem a
    simp only [curveSet, Set.mem_setOf_eq] at this
    rw [← zpow_natCast, ← zpow_mul, ← zpow_mul] at this
    exact this
  have hint := zpow_injective_of_infinite hexp
  -- `q_t - q_s = q_s q_t (h - j)`, impossible unless `h = j`
  set qs : ℤ := ((p ^ s : ℕ) : ℤ) with hqs'
  set qt : ℤ := ((p ^ t : ℕ) : ℤ) with hqt'
  have hqs2 : (2 : ℤ) ≤ qs := by rw [hqs']; exact_mod_cast hqs
  have hqt2 : (2 : ℤ) ≤ qt := by rw [hqt']; exact_mod_cast hqt
  have key : qt - qs = qs * qt * (h - j) := by linear_combination hint
  have hjh : j = h := by
    by_contra hne
    have h1 : (1 : ℤ) ≤ |h - j| := Int.one_le_abs (sub_ne_zero.2 (Ne.symm hne))
    have h2 : |qt - qs| = qs * qt * |h - j| := by
      rw [key, abs_mul, abs_of_pos (by positivity)]
    have h3 : |qt - qs| < qs * qt := by
      rw [abs_lt]; constructor <;> nlinarith
    have h4 : qs * qt * 1 ≤ qs * qt * |h - j| :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  refine ⟨?_, hjh⟩
  subst hjh
  have : qt = qs := by linear_combination key
  have hpow : p ^ s = p ^ t := by
    have := this
    rw [hqs', hqt'] at this
    exact_mod_cast this.symm
  exact Nat.pow_right_injective hp hpow

end ArithDyn.Nilpotence
