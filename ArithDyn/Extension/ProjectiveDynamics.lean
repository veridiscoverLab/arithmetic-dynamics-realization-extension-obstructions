import ArithDyn.Extension.ScaledCoordinateMaps
import ArithDyn.Extension.ScaledProjMapLaws

/-!
# The original quotient's projective dynamical square

The original ideal-preserving map, the chosen coordinate map and the ambient
extension form an equality of actual projective scheme morphisms. The source
is the Proj of the original homogeneous ideal quotient, including nilpotents.
-/

set_option autoImplicit false

noncomputable section

universe u v

open MvPolynomial AlgebraicGeometry CategoryTheory

namespace ArithDyn.Extension

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable {k : Type u} [Field k] {σ ι : Type v} [Finite σ] [Finite ι]

/-- Coordinate congruence modulo the original ideal gives the actual Proj square. -/
theorem scaledProj_commuting_square (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (s d : ℕ) (hs : 0 < s) (hd : 0 < d)
    (j : ι → MvPolynomial σ k) (hj : ∀ i, (j i).IsHomogeneous s)
    (Ψ : ι → MvPolynomial ι k) (hΨ : ∀ i, (Ψ i).IsHomogeneous d)
    (f : σ → MvPolynomial σ k) (hf : ∀ i, (f i).IsHomogeneous d)
    (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hjbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (j i) ≠ 0)
    (hΨbase : ∀ v : ι → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (Ψ i) ≠ 0)
    (hfbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (f i) ≠ 0)
    (hcomm : ∀ i, aeval j (Ψ i) - aeval f (j i) ∈ I) :
    scaledQuotientEndProjMap I hI d hd f hf hpres hfbase ≫
        scaledQuotientCoordinateProjMap I hI s hs j hj hjbase =
      scaledQuotientCoordinateProjMap I hI s hs j hj hjbase ≫
        scaledPolynomialProjMap d hd Ψ hΨ hΨbase := by
  unfold scaledQuotientEndProjMap scaledQuotientCoordinateProjMap scaledPolynomialProjMap
  rw [← DegreeScaledHom.projMap_comp, ← DegreeScaledHom.projMap_comp]
  apply DegreeScaledHom.projMap_congr
  exact (degreeScaledCoordinateMaps_commuting_square I hI s d j hj Ψ hΨ f hf
    hpres hcomm).symm

/-- A square of actual morphisms propagates to all powers of the same endomorphisms. -/
theorem scheme_commuting_square_powers {X Y : Scheme.{u}}
    (f : X ⟶ X) (j : X ⟶ Y) (F : Y ⟶ Y) (h : f ≫ j = j ≫ F) (n : ℕ) :
    ((End.of f) ^ n).asHom ≫ j = j ≫ ((End.of F) ^ n).asHom := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', End.mul_def]
    rw [Category.assoc, h, ← Category.assoc, ih, Category.assoc]

end ArithDyn.Extension
