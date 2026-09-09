import ArithDyn.Extension.ProjCoordinatePolarizationIso
import ArithDyn.Extension.ProjTwistPullbackMate

/-!
# Polarization of the original homogeneous polynomial map

The isomorphism composes the canonical module pullback comparison with the
proved reconstruction in the original polynomial bases.  The same `F`, its
original degree, its actual scheme map, and all transition functions are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open MvPolynomial CategoryTheory AlgebraicGeometry

namespace ArithDyn.Extension.ProjTwist

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra
variable {k : Type u} {σ ι : Type v} [Field k] [Finite σ]

/-- The original degree-`d` map has actual pullback `O(1) ≅ O(d)`. -/
def scaledPolynomialPolarizationIso (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0) :
    (Scheme.Modules.pullback (scaledPolynomialProjMap d hd F hF hbase)).obj
        (standardO k ι 1) ≅ standardO k σ d :=
  pullbackTwistedIso.{u, v} (scaledPolynomialProjMap d hd F hF hbase) (standardCocycle k ι) 1 ≪≫
    polynomialCocycleIso d hd F hF hbase

end ArithDyn.Extension.ProjTwist
