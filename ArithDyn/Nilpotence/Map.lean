import Mathlib

/-!
# The quintic map `T` on `𝔸³` (paper §5, (5.2)) and its orbit formulas

Points of `𝔸³` are `Fin 3 → K` (`0 ↦ x`, `1 ↦ y`, `2 ↦ z`).

* `D(x,y,z) = (y - z) y (x - z)`, `T = (D x z, D x y, D z²)` (5.2).
* Lemma 5.3: points outside `U = {xyz ≠ 0}` reach `O` in at most two steps, and `U` is
  "backward closed" along orbits (5.8).
* Lemma 5.4: `O` is the unique fixed point.
* The exact orbit formula `Tⁿ(uz, vz, z) = (u zₙ, uⁿ v zₙ, zₙ)` ((5.5), (5.7), (5.9)).
* Lemma 5.7 (second part): points over `E` never leave `U`.
-/

set_option autoImplicit false

namespace ArithDyn.Nilpotence

variable {K : Type*} [Field K]

/-- `D(x,y,z) = (y - z) y (x - z)`. -/
def Dq (a : Fin 3 → K) : K := (a 1 - a 2) * a 1 * (a 0 - a 2)

/-- The quintic polynomial map `T = (D x z, D x y, D z²)` (5.2). -/
def T (a : Fin 3 → K) : Fin 3 → K :=
  ![Dq a * a 0 * a 2, Dq a * a 0 * a 1, Dq a * a 2 ^ 2]

/-- The torus `U = {xyz ≠ 0}`. -/
def inU (a : Fin 3 → K) : Prop := a 0 ≠ 0 ∧ a 1 ≠ 0 ∧ a 2 ≠ 0

@[simp] lemma T_zero : T (0 : Fin 3 → K) = 0 := by
  ext i; fin_cases i <;> simp [T, Dq]

lemma T_apply (a : Fin 3 → K) :
    T a 0 = Dq a * a 0 * a 2 ∧ T a 1 = Dq a * a 0 * a 1 ∧ T a 2 = Dq a * a 2 ^ 2 := by
  simp [T]

/-- Lemma 5.4: `O` is the unique fixed point of `T`. -/
theorem fixed_iff (a : Fin 3 → K) : T a = a ↔ a = 0 := by
  constructor
  · intro h
    have h1 : Dq a * a 0 * a 2 = a 0 := by simpa [T] using congrFun h 0
    have h2 : Dq a * a 0 * a 1 = a 1 := by simpa [T] using congrFun h 1
    have h3 : Dq a * a 2 ^ 2 = a 2 := by simpa [T] using congrFun h 2
    by_cases hz : a 2 = 0
    · have hx : a 0 = 0 := by rw [hz, mul_zero] at h1; exact h1.symm
      have hD : Dq a = 0 := by simp [Dq, hx, hz]
      have hy : a 1 = 0 := by rw [hD, zero_mul, zero_mul] at h2; exact h2.symm
      ext i; fin_cases i <;> simp [hx, hy, hz]
    · exfalso
      have hD : Dq a * a 2 = 1 := by
        have : (Dq a * a 2 - 1) * a 2 = 0 := by linear_combination h3
        rcases mul_eq_zero.1 this with h | h
        · linear_combination h
        · exact absurd h hz
      have hD0 : Dq a ≠ 0 := by
        intro h; rw [h, zero_mul] at hD; exact zero_ne_one hD
      have hy : a 1 ≠ 0 := by
        intro hy; apply hD0; simp [Dq, hy]
      have hDx : Dq a * a 0 = 1 := by
        have : (Dq a * a 0 - 1) * a 1 = 0 := by linear_combination h2
        rcases mul_eq_zero.1 this with h | h
        · linear_combination h
        · exact absurd h hy
      have hxz : a 0 = a 2 := by
        have : Dq a * (a 0 - a 2) = 0 := by linear_combination hDx - hD
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hD0
        · linear_combination h
      apply hD0
      simp [Dq, hxz]
  · rintro rfl; simp

/-- Lemma 5.3: a point outside `U` reaches `O` in at most two steps. -/
theorem T_T_eq_zero_of_not_inU {a : Fin 3 → K} (h : ¬ inU a) : T (T a) = 0 := by
  simp only [inU, not_and_or, not_not] at h
  rcases h with hx | hy | hz
  · ext i; fin_cases i <;> simp [T, Dq, hx]
  · ext i; fin_cases i <;> simp [T, Dq, hy]
  · ext i; fin_cases i <;> simp [T, Dq, hz]

/-- If `T a ∈ U` then `a ∈ U`. -/
theorem inU_of_inU_T {a : Fin 3 → K} (h : inU (T a)) : inU a := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, ne_eq, mul_eq_zero, not_or] at h1 h2 h3
  exact ⟨h1.1.2, h2.2, h1.2⟩

/-- (5.8): if `Tᵐ a ∈ U` then all earlier iterates lie in `U`. -/
theorem inU_iterate_of_inU_iterate {a : Fin 3 → K} {m : ℕ} (h : inU (T^[m] a)) :
    ∀ i ≤ m, inU (T^[i] a) := by
  induction m with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    exact h
  | succ m ih =>
    intro i hi
    rw [Function.iterate_succ_apply'] at h
    have h' := inU_of_inU_T h
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact ih h' i (Nat.lt_succ_iff.1 hlt)
    · obtain rfl : i = m + 1 := le_antisymm hi hge
      rw [Function.iterate_succ_apply']
      exact h

/-! ### The orbit formula in the coordinates `(u, v, z)` -/

/-- The radial multiplier along the orbit of `(uz, vz, z)`:
`z₀ = z`, `z_{n+1} = vₙ (vₙ - 1)(u - 1) zₙ⁵` with `vₙ = uⁿ v` (5.5). -/
def zseq (u v z : K) : ℕ → K
  | 0 => z
  | n + 1 => (u ^ n * v) * (u ^ n * v - 1) * (u - 1) * (zseq u v z n) ^ 5

@[simp] lemma zseq_zero (u v z : K) : zseq u v z 0 = z := rfl

lemma zseq_succ (u v z : K) (n : ℕ) :
    zseq u v z (n + 1) = (u ^ n * v) * (u ^ n * v - 1) * (u - 1) * (zseq u v z n) ^ 5 := rfl

/-- (5.5): one step in scaled coordinates. -/
lemma T_scaled (u v z : K) :
    T ![u * z, v * z, z] = ![u * (v * (v - 1) * (u - 1) * z ^ 5),
      (u * v) * (v * (v - 1) * (u - 1) * z ^ 5), v * (v - 1) * (u - 1) * z ^ 5] := by
  ext i; fin_cases i <;> simp [T, Dq] <;> ring

/-- (5.5)/(5.7)/(5.9): `Tⁿ(uz, vz, z) = (u zₙ, uⁿ v zₙ, zₙ)`. -/
theorem iterate_T_scaled (u v z : K) (n : ℕ) :
    T^[n] ![u * z, v * z, z] = ![u * zseq u v z n, u ^ n * v * zseq u v z n, zseq u v z n] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, T_scaled]
    ext i; fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, zseq_succ] <;> ring

/-- Every point with `z ≠ 0` is of the form `(uz, vz, z)`. -/
lemma eq_scaled_of_ne_zero (a : Fin 3 → K) (hz : a 2 ≠ 0) :
    a = ![(a 0 / a 2) * a 2, (a 1 / a 2) * a 2, a 2] := by
  ext i; fin_cases i <;> simp <;> field_simp

/-- Lemma 5.7 (second part): if `u ≠ 0`, `v ≠ 0`, `u ≠ 1`, and `uⁿ v ≠ 1` for all `n`, then the
orbit of `(uz, vz, z)` (`z ≠ 0`) stays in `U` forever; in particular it never reaches `O`. -/
theorem zseq_ne_zero_of_escaping {u v z : K} (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : u ≠ 1)
    (hesc : ∀ n : ℕ, u ^ n * v ≠ 1) (hz : z ≠ 0) (n : ℕ) : zseq u v z n ≠ 0 := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [zseq_succ]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hu) hv)
      (sub_ne_zero.2 (hesc n))) (sub_ne_zero.2 hu1)) (pow_ne_zero _ ih)

/-- Bounded version: `z_N ≠ 0` as soon as the first `N` ratios avoid `1`. -/
theorem zseq_ne_zero_of_lt {u v z : K} (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : u ≠ 1) (hz : z ≠ 0)
    (N : ℕ) (hesc : ∀ n < N, u ^ n * v ≠ 1) : zseq u v z N ≠ 0 := by
  induction N with
  | zero => simpa using hz
  | succ n ih =>
    rw [zseq_succ]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hu) hv)
      (sub_ne_zero.2 (hesc n (Nat.lt_succ_self n)))) (sub_ne_zero.2 hu1))
      (pow_ne_zero _ (ih (fun i hi => hesc i (Nat.lt_succ_of_lt hi))))

theorem inU_iterate_of_escaping {u v z : K} (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : u ≠ 1)
    (hesc : ∀ n : ℕ, u ^ n * v ≠ 1) (hz : z ≠ 0) (n : ℕ) : inU (T^[n] ![u * z, v * z, z]) := by
  rw [iterate_T_scaled]
  have hzn := zseq_ne_zero_of_escaping hu hv hu1 hesc hz n
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.cons_val_zero]; exact mul_ne_zero hu hzn
  · simp only [Matrix.cons_val_one, Matrix.head_cons]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hu) hv) hzn
  · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; exact hzn

theorem iterate_ne_zero_of_escaping {u v z : K} (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : u ≠ 1)
    (hesc : ∀ n : ℕ, u ^ n * v ≠ 1) (hz : z ≠ 0) (n : ℕ) : T^[n] ![u * z, v * z, z] ≠ 0 := by
  intro h
  have := (inU_iterate_of_escaping hu hv hu1 hesc hz n).2.2
  rw [h] at this
  exact this rfl

end ArithDyn.Nilpotence
