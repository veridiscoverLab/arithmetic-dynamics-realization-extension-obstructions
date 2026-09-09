import ArithDyn.Extension.ProjCoordinatePolarizationFrames
import ArithDyn.Extension.ProjTwistReconstruction

/-! # The global module isomorphism supplied by the original polynomial bases -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open MvPolynomial CategoryTheory TopologicalSpace AlgebraicGeometry

namespace ArithDyn.Extension.ProjTwist

/-- Equality of the actual transition functions identifies the reconstructed cocycle. -/
theorem framesCocycle_eq_of_transition {Y : Scheme.{u}} (M : Y.Modules)
    {κ : Type v} (C : UnitCocycle Y κ)
    (e : ∀ i, M.restrict (C.cover i).ι ≅
      SheafOfModules.unit (C.cover i).toScheme.ringCatSheaf)
    (htrans : ∀ (i j : κ) (V : Y.Opens) (hi : V ≤ C.cover i) (hj : V ≤ C.cover j),
      localFrameCoordinates M (e i) V hi ((localFrameCoordinates M (e j) V hj).symm 1) =
        (C.g i j V hi hj : Γ(Y, V))) :
    framesCocycle M C.cover C.covers e = C := by
  cases C with
  | mk cover covers g naturality self comp =>
    dsimp only [framesCocycle]
    congr 1
    funext i j V hi hj
    apply Units.ext
    exact htrans i j V hi hj

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra
variable {k : Type u} {σ ι : Type v} [Field k] [Finite σ]
  (d : ℕ) (hd : 0 < d) (F : ι → MvPolynomial σ k)
  (hF : ∀ i, (F i).IsHomogeneous d)
  (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0)

/-- The bases of the original `O(d)` reconstruct precisely the pulled-back cocycle. -/
theorem polynomialFramesCocycle_eq :
    framesCocycle (standardO k σ d)
        (polynomialPullbackCocycle d hd F hF hbase).cover
        (polynomialPullbackCocycle d hd F hF hbase).covers
        (polynomialPullbackBasis d hd F hF hbase) =
      polynomialPullbackCocycle d hd F hF hbase := by
  apply framesCocycle_eq_of_transition
  intro i j V hi hj
  simp only [polynomialPullbackBasis, localFrameCoordinates_homogeneousBasis]
  simpa only [mul_one] using polynomialPullbackBasis_transition d hd F hF hbase i j V hi hj 1

/-- A genuine global isomorphism from pulled-back matching families to standard
`O(d)`, reconstructed from the same polynomial bases on the entire source cover. -/
def polynomialCocycleIso :
    twistedModule (polynomialPullbackCocycle d hd F hF hbase) 1 ≅ standardO k σ d :=
  ((reconstructFromFramesIso (standardO k σ d)
      (polynomialPullbackCocycle d hd F hF hbase).cover
      (polynomialPullbackCocycle d hd F hF hbase).covers
      (polynomialPullbackBasis d hd F hF hbase)) ≪≫
    eqToIso (congrArg (fun C => twistedModule C 1)
      (polynomialFramesCocycle_eq d hd F hF hbase))).symm

end ArithDyn.Extension.ProjTwist
