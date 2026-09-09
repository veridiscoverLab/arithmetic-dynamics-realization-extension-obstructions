import ArithDyn.Nilpotence.Map
import ArithDyn.Nilpotence.FiniteOrder

/-!
# Pointwise absorption without uniform absorption time (paper §5.3, Proposition 5.5)

`Y_s = {y^q = x z^{q-1}}`, `q = p^s`. Over a field algebraic over `𝔽_p`, every point of `Y_s`
reaches `O`; over an infinite such field there is no `N` with `T^N(Y_s) = {O}`.
-/

set_option autoImplicit false

namespace ArithDyn.Nilpotence

variable {K : Type*} [Field K]

/-- The surface `Y_s = {y^q = x z^{q-1}}` (5.3), as a set of points of `𝔸³`. -/
def Ysurf (q : ℕ) : Set (Fin 3 → K) := {a | a 1 ^ q = a 0 * a 2 ^ (q - 1)}

/-- Points `(t^q z, t z, z)` lie on `Y_s`. -/
lemma param_mem_Ysurf {q : ℕ} (hq : 1 ≤ q) (t z : K) : (![t ^ q * z, t * z, z] : Fin 3 → K) ∈ Ysurf q := by
  simp only [Ysurf, Set.mem_setOf_eq, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.tail_cons]
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-- Every point of `Y_s` with `z ≠ 0` is `(t^q z, t z, z)` with `t = y/z`. -/
lemma Ysurf_eq_param {q : ℕ} (hq : 1 ≤ q) {a : Fin 3 → K} (ha : a ∈ Ysurf q) (hz : a 2 ≠ 0) :
    a = ![(a 1 / a 2) ^ q * a 2, (a 1 / a 2) * a 2, a 2] := by
  have h : a 1 ^ q = a 0 * a 2 ^ (q - 1) := ha
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  ext i; fin_cases i
  · show a 0 = (a 1 / a 2) ^ (q' + 1) * a 2
    rw [div_pow, h, pow_succ]
    field_simp
  · show a 1 = a 1 / a 2 * a 2
    rw [div_mul_cancel₀ _ hz]
  · rfl

/-- Proposition 5.5 (first part): over a field algebraic over `𝔽_p`, every point of `Y_s`
(`s ≥ 1`) reaches `O = 0`. -/
theorem Ysurf_reaches_zero {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K]
    [Algebra.IsAlgebraic (ZMod p) K] {s : ℕ} (hs : 1 ≤ s) {a : Fin 3 → K}
    (ha : a ∈ Ysurf (p ^ s)) : ∃ m : ℕ, 1 ≤ m ∧ T^[m] a = 0 := by
  have hq2 : 2 ≤ p ^ s := le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow (by omega) p)
  have hq1 : 1 ≤ p ^ s := by omega
  by_cases hz : a 2 = 0
  · -- `z = 0` forces `y = 0`, hence `D = 0` and `T a = 0`
    have h : a 1 ^ (p ^ s) = a 0 * a 2 ^ (p ^ s - 1) := ha
    have hy : a 1 = 0 := by
      rw [hz, zero_pow (by omega)] at h
      rw [mul_zero] at h
      exact pow_eq_zero_iff (by omega) |>.1 h
    refine ⟨1, le_rfl, ?_⟩
    simp only [Function.iterate_one]
    ext i; fin_cases i <;> simp [T, Dq, hy]
  · have hparam := Ysurf_eq_param hq1 ha hz
    set t := a 1 / a 2 with ht
    by_cases ht0 : t = 0
    · refine ⟨1, le_rfl, ?_⟩
      have hy : a 1 = 0 := by
        rw [ht, div_eq_zero_iff] at ht0
        exact ht0.resolve_right hz
      simp only [Function.iterate_one]
      ext i; fin_cases i <;> simp [T, Dq, hy]
    by_cases ht1 : t = 1
    · refine ⟨1, le_rfl, ?_⟩
      have hx : a 0 = a 2 := by
        have := congrFun hparam 0
        simp only [Matrix.cons_val_zero] at this
        rw [this, ht1, one_pow, one_mul]
      simp only [Function.iterate_one]
      ext i; fin_cases i <;> simp [T, Dq, hx]
    -- generic case: use finite order
    obtain ⟨n, hn⟩ := exists_pow_shift_eq_one' (p := p) t ht0 s
    refine ⟨n + 1, by omega, ?_⟩
    rw [hparam, iterate_T_scaled]
    have hzn : zseq (t ^ p ^ s) t (a 2) (n + 1) = 0 := by
      rw [zseq_succ]
      have : (t ^ p ^ s) ^ n * t = 1 := by
        rw [← pow_mul, ← hn]; ring
      rw [this, sub_self, mul_zero, zero_mul, zero_mul]
    rw [hzn]
    ext i; fin_cases i <;> simp

/-- The set `{t | t^m = 1}` is finite for `m ≥ 1`. -/
lemma finite_pow_eq_one (m : ℕ) (hm : 0 < m) : Set.Finite {t : K | t ^ m = 1} := by
  apply (Polynomial.finite_setOf_isRoot (Polynomial.X_pow_sub_C_ne_zero hm (1 : K))).subset
  intro t ht
  simp only [Set.mem_setOf_eq] at ht ⊢
  simp [Polynomial.IsRoot, ht]

/-- Proposition 5.5 (second part): over an infinite field, for every `N` there is a point of `Y_s`
whose `N`-th iterate is not `O`; so no single iterate contracts `Y_s` to `O`. -/
theorem exists_Ysurf_iterate_ne_zero [Infinite K] {q : ℕ} (hq : 2 ≤ q) (N : ℕ) :
    ∃ a ∈ Ysurf (K := K) q, T^[N] a ≠ 0 := by
  -- avoid the finitely many bad parameters (5.12)
  have hfin : Set.Finite ({0} ∪ {t : K | t ^ q = 1} ∪
      ⋃ j ∈ Finset.range (N + 1), {t : K | t ^ (1 + j * q) = 1}) := by
    refine ((Set.finite_singleton 0).union (finite_pow_eq_one q (by omega))).union ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun j _ => finite_pow_eq_one _ (by omega))
  obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Set.mem_iUnion, Finset.mem_range, exists_prop, not_or, not_exists, not_and] at ht
  obtain ⟨⟨ht0, htq⟩, htj⟩ := ht
  refine ⟨![t ^ q * 1, t * 1, 1], param_mem_Ysurf (by omega) t 1, ?_⟩
  rw [iterate_T_scaled]
  have hzn : zseq (t ^ q) t 1 N ≠ 0 := by
    -- induction with the bound `n ≤ N`
    have key : ∀ n, n ≤ N → zseq (t ^ q) t 1 n ≠ 0 := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        rw [zseq_succ]
        have h1 : (t ^ q) ^ n * t ≠ 0 := mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ ht0)) ht0
        have h2 : (t ^ q) ^ n * t - 1 ≠ 0 := by
          rw [sub_ne_zero]
          have e : (t ^ q) ^ n * t = t ^ (1 + n * q) := by ring
          rw [e]
          exact htj n (by omega)
        have h3 : t ^ q - 1 ≠ 0 := sub_ne_zero.2 htq
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) (pow_ne_zero _ (ih (by omega)))
    exact key N le_rfl
  intro h
  have := congrFun h 2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply] at this
  exact hzn this

end ArithDyn.Nilpotence
