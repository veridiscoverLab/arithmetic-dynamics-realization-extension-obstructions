import ArithDyn.Extension.ProjCoordinateCocycle
import ArithDyn.Extension.ProjRegrading
import ArithDyn.Extension.SectionAlgebraPullback
import ArithDyn.Extension.ProjTwistPullbackMate

/-!
# Correct twist degrees under positive constant regrading

The coordinate twist of the weighted ring has weighted degree `d`.  Its
transition functions pull back to the standard degree-one transitions through
the actual structure-sheaf regrading map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open MvPolynomial HomogeneousLocalization CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ArithDyn.Extension.ProjTwist

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra
variable {k : Type u} [Field k] {ι : Type v}

/-- The actual regrading pullback retains the same coordinate fraction. -/
theorem regrading_pullRegular_coordinateRatio (d : ℕ) (hd : 0 < d) (i j : ι)
    (U : (Proj (constantWeightGrading ι k d)).Opens)
    (V : (Proj (homogeneousSubmodule ι k)).Opens)
    (hU : U ≤ Proj.basicOpen (constantWeightGrading ι k d) (X i))
    (hV : V ≤ (constantWeightProjIso d hd).hom ⁻¹ᵁ U) :
    pullRegular (constantWeightProjIso d hd).hom hV
      (homogeneousRatio (constantWeightGrading ι k d) (X j) (X i)
        (isWeightedHomogeneous_X k (fun _ : ι => d) j)
        (isWeightedHomogeneous_X k (fun _ : ι => d) i) U hU) =
      homogeneousRatio (homogeneousSubmodule ι k) (X j) (X i)
        (isHomogeneous_X k j) (isHomogeneous_X k i) V
        (hV.trans ((constantWeightProjIso d hd).hom.preimage_mono hU)) := by
  apply Subtype.ext
  funext p
  apply HomogeneousLocalization.val_injective
  change (localizationFromConstantWeight d hd p.1.asHomogeneousIdeal.toIdeal.primeCompl _).val = _
  rw [val_localizationFromConstantWeight]
  rfl

/-- The complete pulled weighted-coordinate cocycle equals the standard one. -/
theorem regrading_pullbackCocycle (d : ℕ) (hd : 0 < d) :
    pullbackCocycle (constantWeightProjIso (k := k) (ι := ι) d hd).hom
      (constantWeightCoordinateCocycle k ι d hd) = standardCocycle k ι := by
  unfold pullbackCocycle standardCocycle homogeneousCocycle
  congr 1
  funext i j V hi hj
  apply Units.ext
  exact regrading_pullRegular_coordinateRatio d hd i j
    (Proj.basicOpen (constantWeightGrading ι k d) (X i) ⊓
      Proj.basicOpen (constantWeightGrading ι k d) (X j)) V inf_le_left (le_inf hi hj)

/-- The weighted coordinate twist of weighted degree `n * d` pulls back to the
standard twist of degree `n`, through the actual regrading scheme isomorphism. -/
def constantWeightTwistPullbackIso (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (Scheme.Modules.pullback (constantWeightProjIso (k := k) (ι := ι) d hd).hom).obj
      (constantWeightCoordinateTwist k ι d hd n) ≅ standardO k ι n :=
  pullbackTwistedIso (constantWeightProjIso d hd).hom
      (constantWeightCoordinateCocycle k ι d hd) n ≪≫
    eqToIso (congrArg (fun C => twistedModule C n) (regrading_pullbackCocycle d hd))

end ArithDyn.Extension.ProjTwist
