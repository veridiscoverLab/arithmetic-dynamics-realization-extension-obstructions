import Mathlib

/-!
# Coefficient descent for polynomial relations at points of the base field

Let `k ⊆ Ω` be fields, `N, D ∈ Ω[X]` with `D ≠ 0`, and suppose that at finitely many points
`a i ∈ k` we have `N (a i) = τ i · D (a i)` with `τ i ∈ k`. Then the same relations are satisfied
by some `N₀, D₀ ∈ k[X]` with `D₀ ≠ 0`, `deg N₀ ≤ deg N` and `deg D₀ ≤ deg D`
(`exists_coeff_descent`). If moreover the points `a i` are pairwise distinct and more numerous
than `deg N + deg D`, then `N · D₀ = N₀ · D` (`coeff_descent_eq`).

Proof of the first statement: the `k`-span `W` of the coefficients of `N` and `D` is
finite-dimensional; choose a `k`-basis `b` of `W` and extend its coordinate functionals to
`k`-linear maps `π j : Ω →ₗ[k] k`. Applying `π j` coefficientwise (`coeffMap`) gives
`N_j, D_j ∈ k[X]` with `N = ∑ j, C (b j) * N_j` and `D = ∑ j, C (b j) * D_j`; the relation at `a i`
becomes `∑ j, (N_j (a i) - τ i · D_j (a i)) • b j = 0` with brackets in `k`, so each bracket
vanishes by linear independence. Since `D ≠ 0`, some `D_j ≠ 0`, and `(N_j, D_j)` works.
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

open Polynomial

section CoeffMap

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Apply a `k`-linear functional `π : Ω →ₗ[k] k` to each coefficient of a polynomial over `Ω`. -/
noncomputable def coeffMap (π : Ω →ₗ[k] k) (p : Polynomial Ω) : k[X] :=
  ⟨Finsupp.mapRange π (map_zero π) p.toFinsupp⟩

@[simp]
theorem coeff_coeffMap (π : Ω →ₗ[k] k) (p : Polynomial Ω) (m : ℕ) :
    (coeffMap π p).coeff m = π (p.coeff m) := by
  simp only [coeffMap, Polynomial.coeff_ofFinsupp, Finsupp.mapRange_apply,
    Polynomial.toFinsupp_apply]

theorem natDegree_coeffMap_le (π : Ω →ₗ[k] k) (p : Polynomial Ω) :
    (coeffMap π p).natDegree ≤ p.natDegree :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => by
    rw [coeff_coeffMap, Polynomial.coeff_eq_zero_of_natDegree_lt hm, map_zero]

/-- If every coefficient `c` of `p` satisfies `c = ∑ j, π j c • β j`, then the value of `p` at a
point of `k` is computed from the values of the descended polynomials `coeffMap (π j) p`. -/
theorem eval_algebraMap_eq_sum_coeffMap {n : ℕ} (β : Fin n → Ω) (π : Fin n → Ω →ₗ[k] k)
    (p : Polynomial Ω) (hp : ∀ m, p.coeff m = ∑ j, π j (p.coeff m) • β j) (r : k) :
    p.eval (algebraMap k Ω r) = ∑ j, ((coeffMap (π j) p).eval r) • β j := by
  have hpoly : p = ∑ j, C (β j) * (coeffMap (π j) p).map (algebraMap k Ω) := by
    ext m
    rw [Polynomial.finset_sum_coeff]
    refine (hp m).trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map, coeff_coeffMap, Algebra.smul_def, mul_comm]
  conv_lhs => rw [hpoly]
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    Algebra.smul_def, mul_comm]

end CoeffMap

/-- The set of coefficients of a polynomial is finite. -/
theorem finite_range_coeff {R : Type*} [Semiring R] (p : R[X]) : (Set.range p.coeff).Finite := by
  refine (((Set.finite_Iic p.natDegree).image p.coeff).insert 0).subset ?_
  rintro _ ⟨m, rfl⟩
  by_cases hm : m ≤ p.natDegree
  · exact Set.mem_insert_iff.mpr (Or.inr ⟨m, hm, rfl⟩)
  · exact Set.mem_insert_iff.mpr
      (Or.inl (Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hm)))

/-- **Coefficient descent.** Relations `N (a i) = τ i · D (a i)` at points `a i ∈ k` with
`τ i ∈ k`, satisfied by `N, D ∈ Ω[X]` with `D ≠ 0`, are also satisfied by some `N₀, D₀ ∈ k[X]`
with `D₀ ≠ 0` and no larger degrees. -/
theorem exists_coeff_descent {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (N D : Polynomial Ω) (hD : D ≠ 0) {ι : Type*} (s : Finset ι) (a τ : ι → k)
    (hrel : ∀ i ∈ s, N.eval (algebraMap k Ω (a i)) =
      algebraMap k Ω (τ i) * D.eval (algebraMap k Ω (a i))) :
    ∃ N₀ D₀ : Polynomial k, D₀ ≠ 0 ∧ N₀.natDegree ≤ N.natDegree ∧ D₀.natDegree ≤ D.natDegree ∧
      ∀ i ∈ s, N₀.eval (a i) = τ i * D₀.eval (a i) := by
  classical
  -- the `k`-span of the coefficients of `N` and `D` is finite-dimensional
  obtain ⟨W, hW⟩ : ∃ W : Submodule k Ω,
      W = Submodule.span k (Set.range N.coeff ∪ Set.range D.coeff) := ⟨_, rfl⟩
  have hNW : ∀ m, N.coeff m ∈ W := fun m => by
    rw [hW]; exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_range_self m))
  have hDW : ∀ m, D.coeff m ∈ W := fun m => by
    rw [hW]; exact Submodule.subset_span (Set.mem_union_right _ (Set.mem_range_self m))
  haveI hfin : FiniteDimensional k W := by
    rw [hW]
    exact FiniteDimensional.span_of_finite k
      ((finite_range_coeff N).union (finite_range_coeff D))
  -- a basis of `W`, and extensions of its coordinate functionals to all of `Ω`
  obtain ⟨n, ⟨b⟩⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) k W) :=
    ⟨_, ⟨Module.finBasis k W⟩⟩
  choose π hπ using fun j : Fin n => LinearMap.exists_extend (b.coord j)
  have hπ' : ∀ j x (hx : x ∈ W), π j x = b.repr ⟨x, hx⟩ j := fun j x hx => by
    have := LinearMap.congr_fun (hπ j) ⟨x, hx⟩
    simpa using this
  have hrepr : ∀ x, x ∈ W → x = ∑ j, π j x • (b j : Ω) := fun x hx => by
    calc x = ((∑ j, b.repr ⟨x, hx⟩ j • b j : W) : Ω) := by rw [b.sum_repr]
      _ = ∑ j, π j x • (b j : Ω) := by
        rw [Submodule.coe_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Submodule.coe_smul, hπ' j x hx]
  have hli : LinearIndependent k fun j => (b j : Ω) := by
    have := b.linearIndependent.map' W.subtype W.ker_subtype
    exact this
  -- the values of `N` and `D` at points of `k`, in terms of the descended polynomials
  have hNev := eval_algebraMap_eq_sum_coeffMap (fun j => (b j : Ω)) π N fun m => hrepr _ (hNW m)
  have hDev := eval_algebraMap_eq_sum_coeffMap (fun j => (b j : Ω)) π D fun m => hrepr _ (hDW m)
  -- the descended relations, by linear independence of the basis
  have hrel' : ∀ j, ∀ i ∈ s,
      (coeffMap (π j) N).eval (a i) = τ i * (coeffMap (π j) D).eval (a i) := by
    intro j i hi
    have h := hrel i hi
    rw [hNev, hDev, ← Algebra.smul_def, Finset.smul_sum] at h
    simp_rw [smul_smul] at h
    have h2 : ∑ j', ((coeffMap (π j') N).eval (a i) - τ i * (coeffMap (π j') D).eval (a i)) •
        (b j' : Ω) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli
      (fun j' => (coeffMap (π j') N).eval (a i) - τ i * (coeffMap (π j') D).eval (a i)) h2 j)
  -- some descended denominator is nonzero
  obtain ⟨m, hm⟩ : ∃ m, D.coeff m ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hD (Polynomial.ext fun m => by rw [h m, Polynomial.coeff_zero])
  obtain ⟨j, hj⟩ : ∃ j, π j (D.coeff m) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hm ((hrepr _ (hDW m)).trans (by simp only [h, zero_smul, Finset.sum_const_zero]))
  refine ⟨coeffMap (π j) N, coeffMap (π j) D, ?_, natDegree_coeffMap_le _ _,
    natDegree_coeffMap_le _ _, hrel' j⟩
  intro h0
  apply hj
  rw [← coeff_coeffMap, h0, Polynomial.coeff_zero]

/-- If the relations `N (a i) = τ i · D (a i)` and `N₀ (a i) = τ i · D₀ (a i)` hold at more than
`deg N + deg D` distinct points, with `deg N₀ ≤ deg N` and `deg D₀ ≤ deg D`, then
`N · D₀ = N₀ · D`. -/
theorem coeff_descent_eq {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (N D : Polynomial Ω) (N₀ D₀ : Polynomial k) {ι : Type*} (s : Finset ι) (a τ : ι → k)
    (hinj : Set.InjOn a ↑s) (hcard : N.natDegree + D.natDegree < s.card)
    (hdeg : N₀.natDegree ≤ N.natDegree) (hdeg' : D₀.natDegree ≤ D.natDegree)
    (hrel : ∀ i ∈ s, N.eval (algebraMap k Ω (a i)) =
      algebraMap k Ω (τ i) * D.eval (algebraMap k Ω (a i)))
    (hrel₀ : ∀ i ∈ s, N₀.eval (a i) = τ i * D₀.eval (a i)) :
    N * D₀.map (algebraMap k Ω) = N₀.map (algebraMap k Ω) * D := by
  classical
  rw [← sub_eq_zero]
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (f := fun i : s => algebraMap k Ω (a i)) _ ?_ ?_ ?_
  · -- the evaluation points are pairwise distinct
    intro i₁ i₂ h
    exact Subtype.ext (hinj i₁.2 i₂.2 ((algebraMap k Ω).injective h))
  · -- the difference vanishes at each evaluation point
    intro i
    have h1 := hrel i i.2
    have h2 := hrel₀ i i.2
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, h1, h2, map_mul]
    ring
  · -- and has degree at most `deg N + deg D < s.card`
    rw [Fintype.card_coe]
    have e1 : (D₀.map (algebraMap k Ω)).natDegree ≤ D.natDegree :=
      Polynomial.natDegree_map_le.trans hdeg'
    have e2 : (N₀.map (algebraMap k Ω)).natDegree ≤ N.natDegree :=
      Polynomial.natDegree_map_le.trans hdeg
    have e4 : (N * D₀.map (algebraMap k Ω)).natDegree ≤ N.natDegree + D.natDegree :=
      Polynomial.natDegree_mul_le.trans (by omega)
    have e5 : (N₀.map (algebraMap k Ω) * D).natDegree ≤ N.natDegree + D.natDegree :=
      Polynomial.natDegree_mul_le.trans (by omega)
    exact ((Polynomial.natDegree_sub_le _ _).trans (max_le e4 e5)).trans_lt hcard

end ArithDyn.Derksen
