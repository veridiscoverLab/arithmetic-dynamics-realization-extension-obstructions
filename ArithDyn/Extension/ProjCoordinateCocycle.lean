import ArithDyn.Extension.ProjTwistHomogeneous
import ArithDyn.Extension.ProjRegradingCore

/-!
# The coordinate cocycle and twists of standard projective space

The standard coordinate opens are `D₊(Xᵢ)`.  The transition from chart `j` to
chart `i` is the actual regular unit `Xⱼ / Xᵢ`.  Thus the matching convention
`aᵢ = gᵢⱼ ^ n * aⱼ` agrees with normalized coefficients `aᵢ = P / Xᵢ ^ n`.
The sheaf `standardO n` is constructed from this concrete cocycle; a line bundle
or a transition system is not supplied as an assumption.

The constant-weight variant uses the same coordinate ratios.  Its `n`-th
cocycle twist corresponds to weighted degree `n * d`, not weighted degree `n`.
All fractions and overlap identities belong to the original structure sheaf.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open MvPolynomial HomogeneousIdeal HomogeneousLocalization
open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace ArithDyn.Extension.ProjTwist

/-- The structure sheaf as its own module.  Binding the scheme before the sheaf
composition instance keeps concrete Proj expressions out of instance search. -/
def unitStructureModule (Y : Scheme.{w}) : SheafOfModules.{w} Y.ringCatSheaf :=
  SheafOfModules.unit Y.ringCatSheaf

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable (k : Type u) (ι : Type v) [Field k]

/-- The actual variable basic opens cover standard Proj. -/
theorem standardCoordinateCover_covers :
    (⨆ i : ι, Proj.basicOpen (homogeneousSubmodule ι k) (X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [standard_irrelevant_eq_coordinateIdeal]

/-- The concrete coordinate transition cocycle `gᵢⱼ = Xⱼ / Xᵢ`. -/
def standardCocycle : UnitCocycle (Proj (homogeneousSubmodule ι k)) ι :=
  homogeneousCocycle (homogeneousSubmodule ι k) X
    (isHomogeneous_X k) (standardCoordinateCover_covers k ι)

@[simp] theorem standardCocycle_cover (i : ι) :
    (standardCocycle k ι).cover i =
      Proj.basicOpen (homogeneousSubmodule ι k) (X i) := rfl

/-- The transition unit is the original homogeneous-localization fraction. -/
@[simp] theorem standardCocycle_g_val (i j : ι)
    (V : (Proj (homogeneousSubmodule ι k)).Opens)
    (hi : V ≤ (standardCocycle k ι).cover i)
    (hj : V ≤ (standardCocycle k ι).cover j) :
    ((standardCocycle k ι).g i j V hi hj : Γ(Proj (homogeneousSubmodule ι k), V)) =
      homogeneousRatio (homogeneousSubmodule ι k) (X j) (X i)
        (isHomogeneous_X k j) (isHomogeneous_X k i) V hi := rfl

/-- The nonnegative standard twist, as an actual sheaf of modules. -/
def standardO (n : ℕ) :
    SheafOfModules.{max u v} (Proj (homogeneousSubmodule ι k)).ringCatSheaf :=
  twistedModule (standardCocycle k ι) n

/-- On every open inside a coordinate chart the constructed twist is the unit module. -/
def standardO_localRestrictionIso (n : ℕ) (i : ι)
    (V : (Proj (homogeneousSubmodule ι k)).Opens)
    (hi : V ≤ Proj.basicOpen (homogeneousSubmodule ι k) (X i)) :
    Scheme.Modules.restrict (standardO k ι n) V.ι ≅
      unitStructureModule V.toScheme :=
  localRestrictionIso.{u, v} (standardCocycle k ι) n i V hi

/-- The same local rank-one trivialization for the actual module pullback. -/
def standardO_localPullbackIso (n : ℕ) (i : ι)
    (V : (Proj (homogeneousSubmodule ι k)).Opens)
    (hi : V ≤ Proj.basicOpen (homogeneousSubmodule ι k) (X i)) :
    (Scheme.Modules.pullback V.ι).obj (standardO k ι n) ≅
      unitStructureModule V.toScheme :=
  localPullbackIso.{u, v} (standardCocycle k ι) n i V hi

/-- The variable opens also cover every positive constant regrading. -/
theorem constantWeightCoordinateCover_covers (d : ℕ) (hd : 0 < d) :
    (⨆ i : ι, Proj.basicOpen (constantWeightGrading ι k d) (X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [constantWeight_irrelevant_eq d hd, standard_irrelevant_eq_coordinateIdeal]

/-- The coordinate cocycle on constant-weight Proj.  One cocycle degree is one
coordinate degree, hence weighted degree `d`. -/
def constantWeightCoordinateCocycle (d : ℕ) (hd : 0 < d) :
    UnitCocycle (Proj (constantWeightGrading ι k d)) ι :=
  homogeneousCocycle (constantWeightGrading ι k d) X
    (isWeightedHomogeneous_X k (fun _ : ι => d))
    (constantWeightCoordinateCover_covers k ι d hd)

@[simp] theorem constantWeightCoordinateCocycle_cover (d : ℕ) (hd : 0 < d) (i : ι) :
    (constantWeightCoordinateCocycle k ι d hd).cover i =
      Proj.basicOpen (constantWeightGrading ι k d) (X i) := rfl

/-- The `n`-th coordinate twist on the constant regrading: its weighted degree
is `n * d`.  This does not identify the weighted degree-one twist with `O(1)`. -/
def constantWeightCoordinateTwist (d : ℕ) (hd : 0 < d) (n : ℕ) :
    SheafOfModules.{max u v} (Proj (constantWeightGrading ι k d)).ringCatSheaf :=
  twistedModule (constantWeightCoordinateCocycle k ι d hd) n

end ArithDyn.Extension.ProjTwist
