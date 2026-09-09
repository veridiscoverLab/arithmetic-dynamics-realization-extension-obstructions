import ArithDyn.Extension.Theorem31

/-!
# From geometric base-point freeness to ideal certificates

The output of `theorem_3_1` has no common nonzero zero over the algebraic closure.
Here this geometric statement is converted into an ideal-theoretic certificate over the
original field.  The certificate applies after evaluation in every commutative algebra,
including nonreduced algebras: a unimodular input vector is sent to a unimodular vector.

The ideal `I` is never replaced by its radical in an equation.  The radical occurs only
in the test that the coordinate sections generate at every prime.  These statements
are ingredients of the passage to `Proj`, not a replacement for constructing its morphisms.
-/

set_option autoImplicit false

namespace ArithDyn.Extension

open MvPolynomial

variable {k σ ι : Type*} [Field k] [Finite σ]

/-- No geometric base point on `V(I)` gives a radical certificate over the original field. -/
theorem coordinateIdeal_le_radical_of_no_basepoint
    (I : Ideal (MvPolynomial σ k)) (F : ι → MvPolynomial σ k)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (F i) ≠ 0) :
    Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (I ⊔ Ideal.span (Set.range F)).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure k)]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨a, rfl⟩
  change X a ∈ vanishingIdeal k (zeroLocus (AlgebraicClosure k)
    (I ⊔ Ideal.span (Set.range F)))
  rw [mem_vanishingIdeal_iff]
  intro v hv
  rw [mem_zeroLocus_iff] at hv
  have hv0 : v = 0 := by
    by_contra h
    obtain ⟨i, hi⟩ := hbase v h (fun g hg => hv g (Ideal.mem_sup_left hg))
    exact hi (hv (F i) (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))))
  simp [hv0]

/-- The globally base-point-free output gives the same certificate without an input ideal. -/
theorem coordinateIdeal_le_radical_of_global_no_basepoint
    (F : ι → MvPolynomial σ k)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0) :
    Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (Ideal.span (Set.range F)).radical := by
  simpa using coordinateIdeal_le_radical_of_no_basepoint (⊥ : Ideal (MvPolynomial σ k)) F
    (fun v hv _ => hbase v hv)

/-- No geometric base point gives a single positive power of the coordinate ideal contained
in the equations plus the output ideal.  This is an ideal containment, not just a pointwise test. -/
theorem exists_coordinateIdeal_pow_le
    (I : Ideal (MvPolynomial σ k)) (F : ι → MvPolynomial σ k)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (F i) ≠ 0) :
    ∃ N : ℕ, 0 < N ∧
      Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ^ N ≤
        I ⊔ Ideal.span (Set.range F) := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (coordinateIdeal_le_radical_of_no_basepoint I F hbase)
    (Submodule.fg_span (Set.finite_range _))
  exact ⟨n + 1, by omega, (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn⟩

/-- In every sufficiently large degree, all homogeneous forms lie in the equations plus
the output-coordinate ideal.  The bound is chosen once for the entire polynomial system. -/
theorem exists_degree_bound_mem_equations_and_coordinates
    (I : Ideal (MvPolynomial σ k)) (F : ι → MvPolynomial σ k)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (F i) ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∀ p : MvPolynomial σ k,
      p.IsHomogeneous n → p ∈ I ⊔ Ideal.span (Set.range F) := by
  obtain ⟨N, hN, hNI⟩ := exists_coordinateIdeal_pow_le I F hbase
  refine ⟨N, hN, fun n hn p hp => hNI ?_⟩
  change p ∈ idealOfVars σ k ^ N
  rw [mem_pow_idealOfVars_iff]
  intro m hm
  have hmn : m.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hm) (hp.coeff_eq_zero h)
  omega

omit [Finite σ] in
/-- Evaluation of the original ideal plus the coordinate ideal lands in the output ideal. -/
theorem map_sup_coordinateIdeal_le {R : Type*} [CommRing R] [Algebra k R]
    (I : Ideal (MvPolynomial σ k)) (F : ι → MvPolynomial σ k) (v : σ → R)
    (hvI : ∀ g ∈ I, aeval v g = 0) :
    (I ⊔ Ideal.span (Set.range F)).map (aeval v) ≤
      Ideal.span (Set.range (fun i => aeval v (F i))) := by
  rw [Ideal.map_le_iff_le_comap, sup_le_iff]
  constructor
  · intro g hg
    change aeval v g ∈ Ideal.span (Set.range (fun i => aeval v (F i)))
    rw [hvI g hg]
    exact Ideal.zero_mem _
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span (Set.mem_range_self i)

/-- A geometric base-point-free system preserves unimodularity over every commutative
`k`-algebra.  In particular this includes algebras with nilpotents. -/
theorem span_evaluated_coordinates_eq_top {R : Type*} [CommRing R] [Algebra k R]
    (I : Ideal (MvPolynomial σ k)) (F : ι → MvPolynomial σ k)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (F i) ≠ 0)
    (v : σ → R) (hvI : ∀ g ∈ I, aeval v g = 0)
    (hv : Ideal.span (Set.range v) = ⊤) :
    Ideal.span (Set.range (fun i => aeval v (F i))) = ⊤ := by
  let J := Ideal.span (Set.range (fun i => aeval v (F i)))
  have hle : Ideal.span (Set.range v) ≤ J.radical := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    have ha := coordinateIdeal_le_radical_of_no_basepoint I F hbase
      (Ideal.subset_span (Set.mem_range_self a))
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha
    refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
    have hn' := map_sup_coordinateIdeal_le I F v hvI
      (Ideal.mem_map_of_mem (aeval v) hn)
    simpa using hn'
  have h1 : (1 : R) ∈ J.radical := hle (by rw [hv]; trivial)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h1
  rw [Ideal.eq_top_iff_one]
  simpa using hn

attribute [local instance] MvPolynomial.gradedAlgebra

omit [Finite σ] in
/-- For the standard grading, Mathlib's irrelevant ideal is exactly the ideal of variables. -/
theorem standard_irrelevant_eq_coordinateIdeal :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ k)).toIdeal =
      Ideal.span (Set.range (X : σ → MvPolynomial σ k)) := by
  apply le_antisymm
  · apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
    intro n hn p hp
    have hp' : p.IsHomogeneous n := (mem_homogeneousSubmodule _ _).mp hp
    change p ∈ idealOfVars σ k
    rw [← pow_one (idealOfVars σ k), mem_pow_idealOfVars_iff]
    intro m hm
    have hmn : m.degree = n := by
      by_contra h
      exact (mem_support_iff.mp hm) (hp'.coeff_eq_zero h)
    omega
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact HomogeneousIdeal.mem_irrelevant_of_mem _ (by omega : 0 < (1 : ℕ))
      ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k a))

end ArithDyn.Extension
