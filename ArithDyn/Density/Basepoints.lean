import ArithDyn.Density.Map

/-!
# Base points, degree, and birationality (paper §4.1, Lemmas 4.3 and 4.4)

* The three coordinate forms of `f` are homogeneous of degree `3`.
* None of `O, E, F` is a point of regularity of `f`: no polynomial representative `G` of the
  rational map (`Gᵢ Fⱼ = Gⱼ Fᵢ`) can be non-vanishing there. This is the formal-arc argument of
  Lemma 4.3, carried out with polynomial arcs `K[t]`.
* `f` is birational: with `g = (A S, B S, ABZ)`, `S = A(A+Z) - BZ`, we have the exact
  identities `g(f(v)) = A³ B R² · v` and `f(g(v)) = A³ B S² · v` (Lemma 4.4).
-/

set_option autoImplicit false

namespace ArithDyn.Density

open MvPolynomial Projectivization

variable {K : Type*} [Field K]

/-- `R = B(A+Z) - AZ` as a polynomial (`X 0 = A`, `X 1 = B`, `X 2 = Z`). -/
noncomputable def Rpoly : MvPolynomial (Fin 3) K := X 1 * (X 0 + X 2) - X 0 * X 2

/-- The three cubic forms `(A R, B R, A² Z)` as polynomials. -/
noncomputable def Fpoly : Fin 3 → MvPolynomial (Fin 3) K :=
  ![X 0 * Rpoly, X 1 * Rpoly, X 0 ^ 2 * X 2]

lemma eval_Rpoly (v : Fin 3 → K) : eval v Rpoly = Rq v := by
  simp [Rpoly, Rq]

lemma eval_Fpoly (v : Fin 3 → K) (i : Fin 3) : eval v (Fpoly i) = Fvec v i := by
  fin_cases i <;> simp [Fpoly, Fvec, Rpoly, Rq]

/-- Lemma 4.3: each coordinate form has degree `3`. -/
lemma Fpoly_isHomogeneous (i : Fin 3) : (Fpoly (K := K) i).IsHomogeneous 3 := by
  have hR : (Rpoly (K := K)).IsHomogeneous 2 := by
    unfold Rpoly
    apply IsHomogeneous.sub
    · exact (isHomogeneous_X K 1).mul ((isHomogeneous_X K 0).add (isHomogeneous_X K 2))
    · exact (isHomogeneous_X K 0).mul (isHomogeneous_X K 2)
  fin_cases i
  · exact (isHomogeneous_X K 0).mul hR
  · exact (isHomogeneous_X K 1).mul hR
  · exact ((isHomogeneous_X K 0).pow 2).mul (isHomogeneous_X K 2)

/-- `f` is *regular at `v`* (in the sense of rational maps to projective space) if some
polynomial representative `G` of the same map, i.e. `Gᵢ Fⱼ = Gⱼ Fᵢ` for all `i, j`, has a
coordinate not vanishing at `v`. -/
def RegularAt (G : Fin 3 → MvPolynomial (Fin 3) K) (v : Fin 3 → K) : Prop :=
  (∀ i j, G i * Fpoly j = G j * Fpoly i) ∧ ∃ i, eval v (G i) ≠ 0

lemma eval_zero_aeval (arc : Fin 3 → Polynomial K) (G : MvPolynomial (Fin 3) K) :
    Polynomial.eval 0 (aeval arc G) = eval (fun i => Polynomial.eval 0 (arc i)) G := by
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- Cancel a nonzero polynomial factor. -/
lemma eq_of_mul_X_pow_eq {p q : Polynomial K} {n : ℕ} (h : p * Polynomial.X ^ n = q * Polynomial.X ^ n) :
    p = q := by
  have : (p - q) * Polynomial.X ^ n = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 this with h' | h'
  · exact sub_eq_zero.1 h'
  · exact absurd h' (pow_ne_zero _ Polynomial.X_ne_zero)

/-- Lemma 4.3: `f` is not regular at `O = [0:0:1]`. -/
theorem not_regularAt_O : ¬ ∃ G : Fin 3 → MvPolynomial (Fin 3) K, RegularAt G ![0, 0, 1] := by
  rintro ⟨G, hrel, i, hi⟩
  -- arc 1: `(t, 0, 1)`
  set φ₁ := aeval (R := K) (![Polynomial.X, 0, 1] : Fin 3 → Polynomial K) with hφ₁
  have hF0 : φ₁ (Fpoly 0) = -Polynomial.X ^ 2 := by
    simp only [hφ₁, Fpoly, Rpoly, Matrix.cons_val_zero, map_mul, map_sub, map_add, aeval_X,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hF1 : φ₁ (Fpoly 1) = 0 := by
    simp only [hφ₁, Fpoly, Rpoly, map_mul, map_sub, map_add, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hF2 : φ₁ (Fpoly 2) = Polynomial.X ^ 2 := by
    simp only [hφ₁, Fpoly, Rpoly, map_mul, map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have e02 := congrArg φ₁ (hrel 0 2)
  rw [map_mul, map_mul, hF2, hF0] at e02
  have h02 : φ₁ (G 0) + φ₁ (G 2) = 0 := by
    have : (φ₁ (G 0) + φ₁ (G 2)) * Polynomial.X ^ 2 = 0 * Polynomial.X ^ 2 := by
      linear_combination e02
    exact eq_of_mul_X_pow_eq this
  have e12 := congrArg φ₁ (hrel 1 2)
  rw [map_mul, map_mul, hF2, hF1, mul_zero] at e12
  have h1 : φ₁ (G 1) = 0 := by
    have : φ₁ (G 1) * Polynomial.X ^ 2 = 0 * Polynomial.X ^ 2 := by rw [e12, zero_mul]
    exact eq_of_mul_X_pow_eq this
  -- arc 2: `(t, t, 1)`
  set φ₂ := aeval (R := K) (![Polynomial.X, Polynomial.X, 1] : Fin 3 → Polynomial K) with hφ₂
  have hF0' : φ₂ (Fpoly 0) = Polynomial.X * Polynomial.X ^ 2 := by
    simp only [hφ₂, Fpoly, Rpoly, Matrix.cons_val_zero, map_mul, map_sub, map_add, aeval_X,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hF2' : φ₂ (Fpoly 2) = Polynomial.X ^ 2 := by
    simp only [hφ₂, Fpoly, Rpoly, map_mul, map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have e02' := congrArg φ₂ (hrel 0 2)
  rw [map_mul, map_mul, hF2', hF0'] at e02'
  have h0' : φ₂ (G 0) = φ₂ (G 2) * Polynomial.X := by
    have : φ₂ (G 0) * Polynomial.X ^ 2 = (φ₂ (G 2) * Polynomial.X) * Polynomial.X ^ 2 := by
      rw [e02']; ring
    exact eq_of_mul_X_pow_eq this
  -- evaluate the arcs at `t = 0`
  have ev₁ : ∀ G', Polynomial.eval 0 (φ₁ G') = eval ![0, 0, 1] G' := by
    intro G'; rw [hφ₁, eval_zero_aeval]
    have : (fun i => Polynomial.eval 0 ((![Polynomial.X, 0, 1] : Fin 3 → Polynomial K) i)) =
        ![0, 0, 1] := by funext j; fin_cases j <;> simp
    rw [this]
  have ev₂ : ∀ G', Polynomial.eval 0 (φ₂ G') = eval ![0, 0, 1] G' := by
    intro G'; rw [hφ₂, eval_zero_aeval]
    have : (fun i => Polynomial.eval 0 ((![Polynomial.X, Polynomial.X, 1] : Fin 3 → Polynomial K) i)) =
        ![0, 0, 1] := by funext j; fin_cases j <;> simp
    rw [this]
  have g0 : eval ![0, 0, 1] (G 0) = 0 := by
    have := congrArg (Polynomial.eval 0) h0'
    rw [ev₂, Polynomial.eval_mul, Polynomial.eval_X, mul_zero] at this
    exact this
  have g1 : eval ![0, 0, 1] (G 1) = 0 := by
    have := congrArg (Polynomial.eval 0) h1
    rwa [ev₁, Polynomial.eval_zero] at this
  have g2 : eval ![0, 0, 1] (G 2) = 0 := by
    have := congrArg (Polynomial.eval 0) h02
    rw [Polynomial.eval_add, ev₁, ev₁, g0, zero_add, Polynomial.eval_zero] at this
    exact this
  fin_cases i
  · exact hi g0
  · exact hi g1
  · exact hi g2

/-- Lemma 4.3: `f` is not regular at `E = [0:1:0]`. -/
theorem not_regularAt_E : ¬ ∃ G : Fin 3 → MvPolynomial (Fin 3) K, RegularAt G ![0, 1, 0] := by
  rintro ⟨G, hrel, i, hi⟩
  -- arc 1: `(t, 1, 0)`, image `(t², t, 0)`
  set φ₁ := aeval (R := K) (![Polynomial.X, 1, 0] : Fin 3 → Polynomial K) with hφ₁
  have hF0 : φ₁ (Fpoly 0) = Polynomial.X * Polynomial.X := by
    simp only [hφ₁, Fpoly, Rpoly, Matrix.cons_val_zero, map_mul, map_sub, map_add, aeval_X,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hF2 : φ₁ (Fpoly 2) = 0 := by
    simp only [hφ₁, Fpoly, Rpoly, map_mul, map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have e20 := congrArg φ₁ (hrel 2 0)
  rw [map_mul, map_mul, hF2, hF0, mul_zero] at e20
  have h2 : φ₁ (G 2) = 0 := by
    have : φ₁ (G 2) * Polynomial.X ^ 2 = 0 * Polynomial.X ^ 2 := by
      rw [zero_mul, pow_two, e20]
    exact eq_of_mul_X_pow_eq this
  -- arc 2: `(t(1-t), 1-t, -t)`, on which `R = 0` and `A²Z = -(t(1-t))² t`
  set φ₂ := aeval (R := K) (![Polynomial.X * (1 - Polynomial.X), 1 - Polynomial.X, -Polynomial.X] :
    Fin 3 → Polynomial K) with hφ₂
  have hR' : φ₂ Rpoly = 0 := by
    simp only [hφ₂, Rpoly, map_mul, map_sub, map_add, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hF0' : φ₂ (Fpoly 0) = 0 := by
    simp [Fpoly, hR']
  have hF1' : φ₂ (Fpoly 1) = 0 := by
    simp [Fpoly, hR']
  have hF2' : φ₂ (Fpoly 2) = -((1 - Polynomial.X) ^ 2 * Polynomial.X ^ 3) := by
    simp only [hφ₂, Fpoly, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hne : (1 - Polynomial.X : Polynomial K) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  have e02 := congrArg φ₂ (hrel 0 2)
  rw [map_mul, map_mul, hF2', hF0', mul_zero] at e02
  have h0 : φ₂ (G 0) = 0 := by
    have : (φ₂ (G 0) * (1 - Polynomial.X) ^ 2) * Polynomial.X ^ 3 = 0 * Polynomial.X ^ 3 := by
      rw [zero_mul]; linear_combination -e02
    have := eq_of_mul_X_pow_eq this
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hne
  have e12 := congrArg φ₂ (hrel 1 2)
  rw [map_mul, map_mul, hF2', hF1', mul_zero] at e12
  have h1 : φ₂ (G 1) = 0 := by
    have : (φ₂ (G 1) * (1 - Polynomial.X) ^ 2) * Polynomial.X ^ 3 = 0 * Polynomial.X ^ 3 := by
      rw [zero_mul]; linear_combination -e12
    have := eq_of_mul_X_pow_eq this
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hne
  have ev₁ : ∀ G', Polynomial.eval 0 (φ₁ G') = eval ![0, 1, 0] G' := by
    intro G'; rw [hφ₁, eval_zero_aeval]
    have : (fun i => Polynomial.eval 0 ((![Polynomial.X, 1, 0] : Fin 3 → Polynomial K) i)) =
        ![0, 1, 0] := by funext j; fin_cases j <;> simp
    rw [this]
  have ev₂ : ∀ G', Polynomial.eval 0 (φ₂ G') = eval ![0, 1, 0] G' := by
    intro G'; rw [hφ₂, eval_zero_aeval]
    have : (fun i => Polynomial.eval 0 ((![Polynomial.X * (1 - Polynomial.X), 1 - Polynomial.X,
        -Polynomial.X] : Fin 3 → Polynomial K) i)) = ![0, 1, 0] := by
      funext j; fin_cases j <;> simp
    rw [this]
  have g0 : eval ![0, 1, 0] (G 0) = 0 := by
    have := congrArg (Polynomial.eval 0) h0; rwa [ev₂, Polynomial.eval_zero] at this
  have g1 : eval ![0, 1, 0] (G 1) = 0 := by
    have := congrArg (Polynomial.eval 0) h1; rwa [ev₂, Polynomial.eval_zero] at this
  have g2 : eval ![0, 1, 0] (G 2) = 0 := by
    have := congrArg (Polynomial.eval 0) h2; rwa [ev₁, Polynomial.eval_zero] at this
  fin_cases i
  · exact hi g0
  · exact hi g1
  · exact hi g2

/-- Lemma 4.3: `f` is not regular at `F = [1:0:0]`. -/
theorem not_regularAt_F : ¬ ∃ G : Fin 3 → MvPolynomial (Fin 3) K, RegularAt G ![1, 0, 0] := by
  rintro ⟨G, hrel, i, hi⟩
  -- arc 1: `(1, t, 0)`, image `(t, t², 0)`
  set φ₁ := aeval (R := K) (![1, Polynomial.X, 0] : Fin 3 → Polynomial K) with hφ₁
  have hF0 : φ₁ (Fpoly 0) = Polynomial.X := by
    simp only [hφ₁, Fpoly, Rpoly, Matrix.cons_val_zero, map_mul, map_sub, map_add, aeval_X,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hF1 : φ₁ (Fpoly 1) = Polynomial.X * Polynomial.X := by
    simp only [hφ₁, Fpoly, Rpoly, map_mul, map_sub, map_add, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hF2 : φ₁ (Fpoly 2) = 0 := by
    simp only [hφ₁, Fpoly, Rpoly, map_mul, map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have e20 := congrArg φ₁ (hrel 2 0)
  rw [map_mul, map_mul, hF2, hF0, mul_zero] at e20
  have h2 : φ₁ (G 2) = 0 := by
    have : φ₁ (G 2) * Polynomial.X ^ 1 = 0 * Polynomial.X ^ 1 := by
      rw [zero_mul, pow_one, e20]
    exact eq_of_mul_X_pow_eq this
  have e10 := congrArg φ₁ (hrel 1 0)
  rw [map_mul, map_mul, hF1, hF0] at e10
  have h1 : φ₁ (G 1) = φ₁ (G 0) * Polynomial.X := by
    have : φ₁ (G 1) * Polynomial.X ^ 1 = (φ₁ (G 0) * Polynomial.X) * Polynomial.X ^ 1 := by
      rw [pow_one, e10]; ring
    exact eq_of_mul_X_pow_eq this
  -- arc 2: `(1, 0, t)`, image `(-t, 0, t)`
  set φ₂ := aeval (R := K) (![1, 0, Polynomial.X] : Fin 3 → Polynomial K) with hφ₂
  have hF0' : φ₂ (Fpoly 0) = -Polynomial.X := by
    simp only [hφ₂, Fpoly, Rpoly, Matrix.cons_val_zero, map_mul, map_sub, map_add, aeval_X,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hF2' : φ₂ (Fpoly 2) = Polynomial.X := by
    simp only [hφ₂, Fpoly, Rpoly, map_mul, map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have e02 := congrArg φ₂ (hrel 0 2)
  rw [map_mul, map_mul, hF2', hF0'] at e02
  have h02 : φ₂ (G 0) + φ₂ (G 2) = 0 := by
    have : (φ₂ (G 0) + φ₂ (G 2)) * Polynomial.X ^ 1 = 0 * Polynomial.X ^ 1 := by
      rw [pow_one]; linear_combination e02
    exact eq_of_mul_X_pow_eq this
  have ev₁ : ∀ G', Polynomial.eval 0 (φ₁ G') = eval ![1, 0, 0] G' := by
    intro G'; rw [hφ₁, eval_zero_aeval]
    have : (fun i => Polynomial.eval 0 ((![1, Polynomial.X, 0] : Fin 3 → Polynomial K) i)) =
        ![1, 0, 0] := by funext j; fin_cases j <;> simp
    rw [this]
  have ev₂ : ∀ G', Polynomial.eval 0 (φ₂ G') = eval ![1, 0, 0] G' := by
    intro G'; rw [hφ₂, eval_zero_aeval]
    have : (fun i => Polynomial.eval 0 ((![1, 0, Polynomial.X] : Fin 3 → Polynomial K) i)) =
        ![1, 0, 0] := by funext j; fin_cases j <;> simp
    rw [this]
  have g2 : eval ![1, 0, 0] (G 2) = 0 := by
    have := congrArg (Polynomial.eval 0) h2; rwa [ev₁, Polynomial.eval_zero] at this
  have g1 : eval ![1, 0, 0] (G 1) = 0 := by
    have := congrArg (Polynomial.eval 0) h1
    rw [ev₁, Polynomial.eval_mul, Polynomial.eval_X, mul_zero] at this
    exact this
  have g0 : eval ![1, 0, 0] (G 0) = 0 := by
    have := congrArg (Polynomial.eval 0) h02
    rw [Polynomial.eval_add, ev₂, ev₂, g2, add_zero, Polynomial.eval_zero] at this
    exact this
  fin_cases i
  · exact hi g0
  · exact hi g1
  · exact hi g2

/-! ### Birationality (Lemma 4.4) -/

/-- `S = A(A+Z) - BZ`. -/
def Sq (v : Fin 3 → K) : K := v 0 * (v 0 + v 2) - v 1 * v 2

/-- The rational inverse `g = (A S, B S, A B Z)`. -/
def Gvec (v : Fin 3 → K) : Fin 3 → K := ![v 0 * Sq v, v 1 * Sq v, v 0 * v 1 * v 2]

/-- `g ∘ f = A³ B R² · id` as an identity of polynomial maps. -/
lemma Gvec_Fvec (v : Fin 3 → K) : Gvec (Fvec v) = (v 0 ^ 3 * v 1 * Rq v ^ 2) • v := by
  ext i; fin_cases i <;> simp [Gvec, Fvec, Sq, Rq] <;> ring

/-- `f ∘ g = A³ B S² · id` as an identity of polynomial maps. -/
lemma Fvec_Gvec (v : Fin 3 → K) : Fvec (Gvec v) = (v 0 ^ 3 * v 1 * Sq v ^ 2) • v := by
  ext i; fin_cases i <;> simp [Gvec, Fvec, Sq, Rq] <;> ring

/-- Lemma 4.4: on the open set `A B R ≠ 0`, `g` is a left inverse of `f` on projective points. -/
theorem g_f_eq {v : Fin 3 → K} (hv : v ≠ 0) (h0 : v 0 ≠ 0) (h1 : v 1 ≠ 0) (hR : Rq v ≠ 0) :
    ∃ hF : Fvec v ≠ 0, ∃ hG : Gvec (Fvec v) ≠ 0, mk K (Gvec (Fvec v)) hG = mk K v hv := by
  have hc : v 0 ^ 3 * v 1 * Rq v ^ 2 ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero _ h0) h1) (pow_ne_zero _ hR)
  have hG : Gvec (Fvec v) ≠ 0 := by rw [Gvec_Fvec]; exact smul_ne_zero hc hv
  have hF : Fvec v ≠ 0 := by
    intro h; apply hG; rw [h]
    ext i; fin_cases i <;> simp [Gvec, Sq]
  refine ⟨hF, hG, ?_⟩
  rw [mk_eq_mk_iff']
  exact ⟨_, (Gvec_Fvec v).symm⟩

/-- Lemma 4.4: every point with `A B S ≠ 0` is in the image of `f` (namely `f(g(P)) = P`);
in particular `f` is dominant. -/
theorem f_g_eq {v : Fin 3 → K} (hv : v ≠ 0) (h0 : v 0 ≠ 0) (h1 : v 1 ≠ 0) (hS : Sq v ≠ 0) :
    ∃ hG : Gvec v ≠ 0, ∃ hF : Fvec (Gvec v) ≠ 0, mk K (Fvec (Gvec v)) hF = mk K v hv := by
  have hc : v 0 ^ 3 * v 1 * Sq v ^ 2 ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero _ h0) h1) (pow_ne_zero _ hS)
  have hF : Fvec (Gvec v) ≠ 0 := by rw [Fvec_Gvec]; exact smul_ne_zero hc hv
  have hG : Gvec v ≠ 0 := by
    intro h; apply hF; rw [h]
    ext i; fin_cases i <;> simp [Fvec, Rq]
  exact ⟨hG, hF, by rw [mk_eq_mk_iff']; exact ⟨_, (Fvec_Gvec v).symm⟩⟩

end ArithDyn.Density
