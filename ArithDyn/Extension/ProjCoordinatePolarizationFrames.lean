import ArithDyn.Extension.ProjCoordinatePolarization
import ArithDyn.Extension.ProjTwistFrames

/-! # The actual local coordinates of the polynomial bases -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open MvPolynomial HomogeneousLocalization CategoryTheory TopologicalSpace AlgebraicGeometry

namespace ArithDyn.Extension.ProjTwist

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra
variable {k : Type u} {σ : Type v} [Field k]

/-- Evaluating the actual basis isomorphism gives the constructed division map. -/
theorem frameCoordinatesOnImage_homogeneousBasis (d : ℕ) (F : MvPolynomial σ k)
    (hF : F.IsHomogeneous d) (U : (Proj (homogeneousSubmodule σ k)).Opens)
    (hU : U ≤ Proj.basicOpen (homogeneousSubmodule σ k) F) (W : U.toScheme.Opens) :
    frameCoordinatesOnImage (standardO k σ d)
        (homogeneousBasisRestrictionIso d F hF U hU) W =
      homogeneousBasisLinearEquiv d F hF (U.ι ''ᵁ W) ((U.ι_image_le W).trans hU) := by
  ext a
  rfl

/-- The original-open coordinates, including their open-set transports, are the
same division-by-`F` map on every smaller open. -/
theorem localFrameCoordinates_homogeneousBasis (d : ℕ) (F : MvPolynomial σ k)
    (hF : F.IsHomogeneous d) (U : (Proj (homogeneousSubmodule σ k)).Opens)
    (hU : U ≤ Proj.basicOpen (homogeneousSubmodule σ k) F)
    (V : (Proj (homogeneousSubmodule σ k)).Opens) (hV : V ≤ U) :
    localFrameCoordinates (standardO k σ d)
        (homogeneousBasisRestrictionIso d F hF U hU) V hV =
      homogeneousBasisLinearEquiv d F hF V (hV.trans hU) := by
  ext a
  rw [localFrameCoordinates_apply, frameCoordinatesOnImage_homogeneousBasis]
  change res (image_preimage_eq_of_le hV).symm.le
      (homogeneousBasisLinearEquiv d F hF (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))
        ((U.ι_image_le (U.ι ⁻¹ᵁ V)).trans hU)
        (restrictSections (standardCocycle k σ) d (image_preimage_eq_of_le hV).le a)) = _
  rw [homogeneousBasisLinearEquiv_restrict d F hF
    (image_preimage_eq_of_le hV).le (hV.trans hU), res_comp, res_refl]
  rfl

end ArithDyn.Extension.ProjTwist
