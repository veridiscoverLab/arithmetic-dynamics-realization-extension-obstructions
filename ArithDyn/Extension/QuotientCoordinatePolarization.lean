import ArithDyn.Extension.ProjectiveCoordinateRestriction
import ArithDyn.Extension.ProjPolynomialPolarization

/-!
# Standard twists on the original projective quotient

The line-bundle comparison uses the actual coordinate inclusion and the actual
restriction factorization.  The original quotient is never reduced.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open MvPolynomial AlgebraicGeometry CategoryTheory
namespace ArithDyn.Extension
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra
variable {k : Type u} [Field k] {σ ι : Type v} [Finite σ]

/-- The standard twist restricted to the original projective quotient. -/
def quotientCoordinateTwist (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    (Proj (polynomialQuotientGrading I hI)).Modules :=
  (Scheme.Modules.pullback (quotientCoordinateInclusion I hI)).obj
    (ProjTwist.standardO k σ n)

/-- Restricting the same global homogeneous coordinates preserves their true
pullback formula on the original quotient. -/
def quotientCoordinatePolarizationIso (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (d : ℕ) (hd : 0 < d) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0) :
    (Scheme.Modules.pullback (scaledQuotientCoordinateProjMap I hI d hd F hF
      (fun v hv _ => hbase v hv))).obj (ProjTwist.standardO k ι 1) ≅
        quotientCoordinateTwist I hI d :=
  (Scheme.Modules.pullbackCongr
    (quotientCoordinateInclusion_comp I hI d hd F hF hbase).symm).app
      (ProjTwist.standardO k ι 1) ≪≫
    ((Scheme.Modules.pullbackComp (quotientCoordinateInclusion I hI)
      (scaledPolynomialProjMap d hd F hF hbase)).app (ProjTwist.standardO k ι 1)).symm ≪≫
    (Scheme.Modules.pullback (quotientCoordinateInclusion I hI)).mapIso
      (ProjTwist.scaledPolynomialPolarizationIso d hd F hF hbase)

end ArithDyn.Extension
