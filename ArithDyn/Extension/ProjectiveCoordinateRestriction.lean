import ArithDyn.Extension.ProjectiveDynamics

/-!
# Restriction of global homogeneous coordinates to the original projective quotient

All maps below keep the original ideal.  This gives the actual restriction
factorization needed to pull back the standard twists to that quotient.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open MvPolynomial AlgebraicGeometry CategoryTheory
namespace ArithDyn.Extension
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra
variable {k : Type u} [Field k] {σ ι : Type v} [Finite σ]

omit [Finite σ] in
/-- The original variable coordinates have no base point on any original quotient. -/
theorem variableCoordinates_no_basepoint (I : Ideal (MvPolynomial σ k)) :
    ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (X i : MvPolynomial σ k) ≠ 0 := by
  intro v hv _
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact ⟨i, by simpa only [aeval_X, Pi.zero_apply] using hi⟩

/-- The actual coordinate inclusion of the original projective quotient. -/
def quotientCoordinateInclusion (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) :
    Proj (polynomialQuotientGrading I hI) ⟶ Proj (homogeneousSubmodule σ k) :=
  scaledQuotientCoordinateProjMap I hI 1 Nat.zero_lt_one X (isHomogeneous_X k)
    (variableCoordinates_no_basepoint I)

/-- Restricting a global coordinate map is exactly the coordinate map on the original quotient. -/
theorem quotientCoordinateInclusion_comp (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (d : ℕ) (hd : 0 < d) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0) :
    quotientCoordinateInclusion I hI ≫ scaledPolynomialProjMap d hd F hF hbase =
      scaledQuotientCoordinateProjMap I hI d hd F hF (fun v hv _ => hbase v hv) := by
  unfold quotientCoordinateInclusion scaledPolynomialProjMap scaledQuotientCoordinateProjMap
  rw [← DegreeScaledHom.projMap_comp]
  apply DegreeScaledHom.projMap_congr
  apply RingHom.ext
  intro p
  change Ideal.Quotient.mk I (aeval (X : σ → MvPolynomial σ k) (aeval F p)) =
    Ideal.Quotient.mk I (aeval F p)
  congr 1
  simp

omit [Finite σ] in
/-- The full Veronese generation certificate makes the same coordinates globally
base-point-free, even before restriction to the original quotient. -/
theorem exact_veronese_no_basepoint (s : ℕ)
    (j : ι → MvPolynomial σ k)
    (hgen : ∀ (n : ℕ) (g : MvPolynomial σ k), g.IsHomogeneous (n * s) →
      ∃ G : MvPolynomial ι k, G.IsHomogeneous n ∧ aeval j G = g) :
    ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (j i) ≠ 0 := by
  intro v hv
  by_contra h
  push Not at h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  obtain ⟨G, hG, hGj⟩ := hgen 1 ((X i) ^ s)
    (by simpa only [one_mul] using (isHomogeneous_X k i).pow s)
  have hG0 : constantCoeff G = 0 := by
    change coeff (0 : ι →₀ ℕ) G = 0
    apply hG.coeff_eq_zero
    simp
  have hz : (fun a => aeval v (j a)) = (0 : ι → AlgebraicClosure k) := funext h
  have heval : aeval v ((X i : MvPolynomial σ k) ^ s) = 0 := by
    rw [← hGj, comp_aeval_apply, hz, aeval_zero, hG0, map_zero]
  rw [map_pow, aeval_X] at heval
  exact (pow_ne_zero s hi) heval

end ArithDyn.Extension
