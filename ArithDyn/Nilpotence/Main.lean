import ArithDyn.Nilpotence.Elimination
import ArithDyn.Nilpotence.EliminationOpen
import ArithDyn.Nilpotence.Collision
import ArithDyn.Nilpotence.Pointwise

/-!
# No universal geometrically nilpotent seed (paper §5, Theorem 5.2)

Combining the elimination tool (`exists_vanishing_poly`) with the exponent-collision lemma we
prove (5.4): for every closed geometrically nilpotent `Y = V F ⊆ 𝔸³_K`, all but finitely many of
the surfaces `Y_s = {y^{p^s} = x z^{p^s-1}}` satisfy `T^k(Y_s) ⊄ closure(T^m(Y))` for all `k, m`.
-/

set_option autoImplicit false

namespace ArithDyn.Nilpotence

open MvPolynomial Finset

variable {K : Type*} [Field K]

/-- Zariski closure of a set of points of `𝔸³`. -/
def zariskiClosure (S : Set (Fin 3 → K)) : Set (Fin 3 → K) :=
  {a | ∀ f : MvPolynomial (Fin 3) K, (∀ s ∈ S, eval s f = 0) → eval a f = 0}

lemma subset_zariskiClosure (S : Set (Fin 3 → K)) : S ⊆ zariskiClosure S :=
  fun a ha f hf => hf a ha

/-- Definition 5.1: `Y` is geometrically nilpotent if every point of `Y` eventually reaches a
common fixed point `P` of `T` (by Lemma 5.4, necessarily `P = O`). -/
def GeomNilpotent (Y : Set (Fin 3 → K)) : Prop :=
  ∃ P, T P = P ∧ ∀ y ∈ Y, ∃ n, 1 ≤ n ∧ T^[n] y = P

lemma GeomNilpotent.reach_zero {Y : Set (Fin 3 → K)} (h : GeomNilpotent Y) :
    ∀ y ∈ Y, ∃ n, 1 ≤ n ∧ T^[n] y = 0 := by
  obtain ⟨P, hP, h⟩ := h
  rw [fixed_iff] at hP
  subst hP
  exact h

/-- `Y_s` is the closed set `V {y^q - x z^{q-1}}`. -/
lemma Ysurf_eq_V (q : ℕ) :
    Ysurf (K := K) q = V {X 1 ^ q - X 0 * X 2 ^ (q - 1)} := by
  ext a
  simp [Ysurf, V, sub_eq_zero]

/-- The polynomial `H_m` (cf. (5.17)): it vanishes on `T^m(V F)`. -/
noncomputable def Hpoly (d : MvPolynomial (Fin 2) K) (m : ℕ) : MvPolynomial (Fin 3) K :=
  X 0 * X 1 * X 2 * subst3 d (fun s => s 1 + m * (d.totalDegree - s 0)) (fun s => s 0)
    (fun s => d.totalDegree - s 1 - s 0 + s 0 * m)

lemma eval_subst3_scaled (d : MvPolynomial (Fin 2) K) (m : ℕ) (u w z : K) :
    eval ![u * z, w * z, z] (subst3 d (fun s => s 1 + m * (d.totalDegree - s 0)) (fun s => s 0)
      (fun s => d.totalDegree - s 1 - s 0 + s 0 * m)) =
    z ^ ((m + 1) * d.totalDegree) *
      ∑ s ∈ d.support, coeff s d * (u ^ (s 1 + m * (d.totalDegree - s 0)) * w ^ s 0) := by
  rw [eval_subst3, mul_sum]
  refine sum_congr rfl (fun s hs => ?_)
  have h := support_le_totalDegree hs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [monomial_identity u w z (α := s 1) (β := s 0) (by omega) (by omega)]
  ring

lemma term_identity (c u v : K) (a0 a1 m D₁ : ℕ) :
    c * (u ^ (a1 + m * D₁) * (u ^ m * v) ^ a0) = u ^ (m * (a0 + D₁)) * (c * (v ^ a0 * u ^ a1)) := by
  rw [mul_pow, ← pow_mul]
  have h1 : u ^ (a1 + m * D₁) * (u ^ (m * a0) * v ^ a0) = u ^ (a1 + m * D₁ + m * a0) * v ^ a0 := by
    rw [pow_add u (a1 + m * D₁) (m * a0), mul_assoc]
  have h2 : u ^ (m * (a0 + D₁)) * (c * (v ^ a0 * u ^ a1)) =
      c * (u ^ (m * (a0 + D₁) + a1) * v ^ a0) := by
    rw [pow_add u (m * (a0 + D₁)) a1]
    ac_rfl
  rw [h1, h2]
  congr 3
  ring

lemma term_identity' (c t : K) (a0 a1 q m k D' : ℕ) :
    c * ((t ^ q) ^ (a1 + m * D') * ((t ^ q) ^ k * t) ^ a0) =
      c * t ^ (q * (a1 + m * D' + k * a0) + a0) := by
  have e1 : ((t ^ q) ^ k * t) ^ a0 = t ^ ((q * k + 1) * a0) := by
    rw [← pow_mul, ← pow_succ, ← pow_mul]
  have e2 : (t ^ q) ^ (a1 + m * D') = t ^ (q * (a1 + m * D')) := by rw [← pow_mul]
  rw [e1, e2, ← pow_add]
  congr 2
  ring

/-- `H_m` vanishes on `T^m(Y)` when `d` vanishes on `π(Y ∩ U)` (any set `Y ⊆ 𝔸³`). -/
lemma Hpoly_vanish {Y : Set (Fin 3 → K)} {d : MvPolynomial (Fin 2) K}
    (hd : ∀ y ∈ Y, inU y → eval ![y 1 / y 2, y 0 / y 2] d = 0) (m : ℕ) :
    ∀ a ∈ T^[m] '' Y, eval a (Hpoly d m) = 0 := by
  rintro a ⟨y, hy, rfl⟩
  by_cases hU : inU (T^[m] y)
  · have hyU : inU y := inU_iterate_of_inU_iterate hU 0 (Nat.zero_le _)
    have hz : y 2 ≠ 0 := hyU.2.2
    have hd' : eval ![y 1 / y 2, y 0 / y 2] d = 0 := hd y hy hyU
    have hy' : y = ![(y 0 / y 2) * y 2, (y 1 / y 2) * y 2, y 2] := eq_scaled_of_ne_zero y hz
    have hsum : ∑ s ∈ d.support, coeff s d *
        ((y 0 / y 2) ^ (s 1 + m * (d.totalDegree - s 0)) * ((y 0 / y 2) ^ m * (y 1 / y 2)) ^ s 0) =
        (y 0 / y 2) ^ (m * d.totalDegree) * eval ![y 1 / y 2, y 0 / y 2] d := by
      rw [eval_two, mul_sum]
      refine sum_congr rfl (fun s hs => ?_)
      have h := support_le_totalDegree hs
      obtain ⟨D₁, hD₁⟩ := Nat.exists_eq_add_of_le (show s 0 ≤ d.totalDegree by omega)
      have e : d.totalDegree - s 0 = D₁ := by omega
      rw [e, hD₁]
      generalize s 0 = a0
      generalize s 1 = a1
      exact term_identity _ _ _ _ _ _ _
    rw [Hpoly, map_mul, hy', iterate_T_scaled, eval_subst3_scaled, hsum, hd', mul_zero, mul_zero,
      mul_zero]
  · rw [Hpoly, map_mul, map_mul, map_mul]
    simp only [eval_X]
    simp only [inU, not_and_or, not_not] at hU
    rcases hU with h | h | h <;> simp [h]

/-- The exponent map `ℓ` of the one-variable polynomial along the parametrised curve. -/
def ell (d : MvPolynomial (Fin 2) K) (q m k : ℕ) (s : Fin 2 →₀ ℕ) : ℕ :=
  q * (s 1 + m * (d.totalDegree - s 0) + k * s 0) + s 0

lemma eval_Hpoly_param (d : MvPolynomial (Fin 2) K) (q m k : ℕ) (t : K) :
    eval (T^[k] ![t ^ q * 1, t * 1, 1]) (Hpoly d m) =
      (t ^ q * zseq (t ^ q) t 1 k) * ((t ^ q) ^ k * t * zseq (t ^ q) t 1 k) * zseq (t ^ q) t 1 k *
        (zseq (t ^ q) t 1 k ^ ((m + 1) * d.totalDegree) * (ppoly d (ell d q m k)).eval t) := by
  have hsum : ∑ s ∈ d.support, coeff s d *
      ((t ^ q) ^ (s 1 + m * (d.totalDegree - s 0)) * ((t ^ q) ^ k * t) ^ s 0) =
      (ppoly d (ell d q m k)).eval t := by
    rw [ppoly_eval]
    refine sum_congr rfl (fun s _ => ?_)
    simp only [ell]
    generalize d.totalDegree - s 0 = D'
    generalize s 0 = a0
    generalize s 1 = a1
    exact term_identity' _ _ _ _ _ _ _ _
  rw [Hpoly, iterate_T_scaled, map_mul, eval_subst3_scaled, hsum]
  simp only [map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- Finitely many parameters `t` are excluded (cf. (5.12)). -/
lemma finite_bad_param [Infinite K] (q k : ℕ) (hq : 1 ≤ q) :
    Set.Finite {t : K | t = 0 ∨ zseq (t ^ q) t 1 k = 0} := by
  have hfin : Set.Finite ({0} ∪ {t : K | t ^ q = 1} ∪
      ⋃ n ∈ Finset.range k, {t : K | t ^ (q * n + 1) = 1}) := by
    refine ((Set.finite_singleton 0).union (finite_pow_eq_one q (by omega))).union ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun n _ => finite_pow_eq_one _ (by omega))
  apply hfin.subset
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  by_contra hcon
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_iUnion,
    Finset.mem_range, exists_prop, not_or, not_exists, not_and] at hcon
  obtain ⟨⟨ht0, htq⟩, htn⟩ := hcon
  rcases ht with h | h
  · exact ht0 h
  · apply zseq_ne_zero_of_lt (pow_ne_zero _ ht0) ht0 htq one_ne_zero k _ h
    intro n hn
    have := htn n hn
    rwa [pow_add, pow_one, pow_mul] at this

/-- **(5.4), general form.** If `d ≠ 0` vanishes on `π(Y ∩ U)` and `q > deg d`, then for all
`k, m`, `T^k(Y_q) ⊄ closure(T^m(Y))` (any set `Y ⊆ 𝔸³`). -/
theorem not_subset_closure_of_lt [Infinite K] {Y : Set (Fin 3 → K)}
    {d : MvPolynomial (Fin 2) K} (hd0 : d ≠ 0)
    (hd : ∀ y ∈ Y, inU y → eval ![y 1 / y 2, y 0 / y 2] d = 0)
    {q : ℕ} (hq : d.totalDegree < q) (k m : ℕ) :
    ¬ (T^[k] '' Ysurf q ⊆ zariskiClosure (T^[m] '' Y)) := by
  intro hsub
  have hq1 : 1 ≤ q := by omega
  have hP : ppoly d (ell d q m k) ≠ 0 := ppoly_ne_zero d _ hd0 (ell_injOn d hq)
  have hvan : ∀ t : K, t ≠ 0 → zseq (t ^ q) t 1 k ≠ 0 → (ppoly d (ell d q m k)).eval t = 0 := by
    intro t ht hz
    have hmem : T^[k] ![t ^ q * 1, t * 1, 1] ∈ zariskiClosure (T^[m] '' Y) :=
      hsub ⟨_, param_mem_Ysurf hq1 t 1, rfl⟩
    have h0 := hmem (Hpoly d m) (Hpoly_vanish hd m)
    rw [eval_Hpoly_param] at h0
    have htq : t ^ q ≠ 0 := pow_ne_zero _ ht
    simpa [htq, ht, hz] using h0
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (finite_bad_param q k hq1).infinite_compl.mono
  intro t ht
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or] at ht
  exact hvan t ht.1 ht.2

/-- **Theorem 5.2, (5.4).** Over an algebraically closed field in which every nonzero element is a
root of unity (e.g. `\bar 𝔽_p`), for every closed geometrically nilpotent `Y = V F ⊆ 𝔸³` there is
`s₀` such that for all `s ≥ s₀` and all `k, m ≥ 0`, `T^k(Y_s) ⊄ closure(T^m(Y))`,
where `Y_s = {y^{p^s} = x z^{p^s - 1}}`. -/
theorem no_universal_seed [IsAlgClosed K]
    (hfin : ∀ u : K, u ≠ 0 → ∃ M : ℕ, 0 < M ∧ u ^ M = 1) {p : ℕ} (hp : 2 ≤ p)
    (F : Set (MvPolynomial (Fin 3) K)) (hnil : GeomNilpotent (V F)) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ k m : ℕ,
      ¬ (T^[k] '' Ysurf (p ^ s) ⊆ zariskiClosure (T^[m] '' V F)) := by
  obtain ⟨d, hd0, hd⟩ := exists_vanishing_poly hfin F hnil.reach_zero
  refine ⟨d.totalDegree + 1, fun s hs k m => ?_⟩
  apply not_subset_closure_of_lt hd0 hd _ k m
  calc d.totalDegree < s := by omega
    _ < p ^ s := Nat.lt_pow_self (by omega)

/-- **Theorem 5.2, (5.4), locally closed case.** The same conclusion for a geometrically nilpotent
locally closed set `Y = V F \ V G`. -/
theorem no_universal_seed_locallyClosed [IsAlgClosed K]
    (hfin : ∀ u : K, u ≠ 0 → ∃ M : ℕ, 0 < M ∧ u ^ M = 1) {p : ℕ} (hp : 2 ≤ p)
    (F G : Set (MvPolynomial (Fin 3) K)) (hnil : GeomNilpotent (V F \ V G)) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ k m : ℕ,
      ¬ (T^[k] '' Ysurf (p ^ s) ⊆ zariskiClosure (T^[m] '' (V F \ V G))) := by
  obtain ⟨d, hd0, hd⟩ := exists_vanishing_poly_locallyClosed hfin F G hnil.reach_zero
  refine ⟨d.totalDegree + 1, fun s hs k m => ?_⟩
  apply not_subset_closure_of_lt hd0 hd _ k m
  calc d.totalDegree < s := by omega
    _ < p ^ s := Nat.lt_pow_self (by omega)

/-- Borisov's question (5.1) has a negative answer: no closed geometrically nilpotent `Y` covers
all `Y_s` by `(T^k)^{-1}(T^m(Y))`. -/
theorem no_universal_seed' [IsAlgClosed K]
    (hfin : ∀ u : K, u ≠ 0 → ∃ M : ℕ, 0 < M ∧ u ^ M = 1) {p : ℕ} (hp : 2 ≤ p)
    (F : Set (MvPolynomial (Fin 3) K)) (hnil : GeomNilpotent (V F)) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ k m : ℕ, ¬ (Ysurf (p ^ s) ⊆ T^[k] ⁻¹' (T^[m] '' V F)) := by
  obtain ⟨s₀, h⟩ := no_universal_seed hfin hp F hnil
  refine ⟨s₀, fun s hs k m hsub => h s hs k m ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact subset_zariskiClosure _ (hsub hy)

/-- (5.1) for locally closed `Y`. -/
theorem no_universal_seed_locallyClosed' [IsAlgClosed K]
    (hfin : ∀ u : K, u ≠ 0 → ∃ M : ℕ, 0 < M ∧ u ^ M = 1) {p : ℕ} (hp : 2 ≤ p)
    (F G : Set (MvPolynomial (Fin 3) K)) (hnil : GeomNilpotent (V F \ V G)) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ k m : ℕ, ¬ (Ysurf (p ^ s) ⊆ T^[k] ⁻¹' (T^[m] '' (V F \ V G))) := by
  obtain ⟨s₀, h⟩ := no_universal_seed_locallyClosed hfin hp F G hnil
  refine ⟨s₀, fun s hs k m hsub => h s hs k m ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact subset_zariskiClosure _ (hsub hy)

/-! ### The concrete case `K = \bar 𝔽_p` -/

/-- Every `Y_s` (`s ≥ 1`) is geometrically nilpotent over `\bar 𝔽_p` (Proposition 5.5). -/
theorem Ysurf_geomNilpotent (p : ℕ) [Fact p.Prime] {s : ℕ} (hs : 1 ≤ s) :
    GeomNilpotent (Ysurf (K := AlgebraicClosure (ZMod p)) (p ^ s)) :=
  ⟨0, T_zero, fun a ha => Ysurf_reaches_zero (p := p) hs ha⟩

/-- **Theorem 5.2 over `\bar 𝔽_p`.** -/
theorem theorem_5_2 (p : ℕ) [Fact p.Prime]
    (F : Set (MvPolynomial (Fin 3) (AlgebraicClosure (ZMod p))))
    (hnil : GeomNilpotent (V F)) :
    -- `O` is the unique fixed point
    (∀ a : Fin 3 → AlgebraicClosure (ZMod p), T a = a ↔ a = 0) ∧
    -- each `Y_s` is geometrically nilpotent but not nilpotent
    (∀ s, 1 ≤ s → GeomNilpotent (Ysurf (K := AlgebraicClosure (ZMod p)) (p ^ s))) ∧
    (∀ s, 1 ≤ s → ∀ N, ∃ a ∈ Ysurf (K := AlgebraicClosure (ZMod p)) (p ^ s), T^[N] a ≠ 0) ∧
    -- (5.4)
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ k m : ℕ,
      ¬ (T^[k] '' Ysurf (p ^ s) ⊆ zariskiClosure (T^[m] '' V F)) := by
  refine ⟨fixed_iff, fun s hs => Ysurf_geomNilpotent p hs, ?_, ?_⟩
  · intro s hs N
    have hq : 2 ≤ p ^ s := le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow (by omega) p)
    exact exists_Ysurf_iterate_ne_zero hq N
  · exact no_universal_seed (forall_exists_pow_eq_one p) (Fact.out : p.Prime).two_le F hnil

/-- **Theorem 5.2 over `\bar 𝔽_p`, locally closed `Y = V F \ V G`.** -/
theorem theorem_5_2_locallyClosed (p : ℕ) [Fact p.Prime]
    (F G : Set (MvPolynomial (Fin 3) (AlgebraicClosure (ZMod p))))
    (hnil : GeomNilpotent (V F \ V G)) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ k m : ℕ,
      ¬ (T^[k] '' Ysurf (p ^ s) ⊆ zariskiClosure (T^[m] '' (V F \ V G))) :=
  no_universal_seed_locallyClosed (forall_exists_pow_eq_one p) (Fact.out : p.Prime).two_le F G hnil

end ArithDyn.Nilpotence
