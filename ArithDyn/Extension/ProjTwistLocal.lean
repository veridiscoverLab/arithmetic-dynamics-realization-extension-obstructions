import ArithDyn.Extension.ProjTwistSheaf
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Local rank-one coordinates of the actual cocycle sheaf

On any open lying in a chart, all coefficients are recovered from the single
chart coefficient by the original transition cocycle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u v
open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{u}} {ι : Type v} (C : UnitCocycle X ι)

/-- Expand one chart coefficient into its full compatible family. -/
def fromLocal (n : ℕ) (j : ι) (V : X.Opens) (hj : V ≤ C.cover j)
    (a : Γ(X, V)) : TwistedSections C n V := by
  refine ⟨fun i =>
    (C.g i j (V ⊓ C.cover i) inf_le_right (inf_le_left.trans hj) :
      Γ(X, V ⊓ C.cover i)) ^ n * res inf_le_left a, ?_⟩
  intro i k
  simp only [map_mul, map_pow, res_g, res_comp]
  have h := congrArg (fun z : Γ(X, overlap C V i k)ˣ => (z : Γ(X, overlap C V i k)))
    (C.comp i k j (overlap C V i k)
      (inf_le_left.trans inf_le_right) inf_le_right
      ((inf_le_left.trans inf_le_left).trans hj))
  simp only [Units.val_mul] at h
  rw [← h, mul_pow]
  ring

/-- Read the chosen chart coefficient on an open contained in that chart. -/
def toLocal (n : ℕ) (j : ι) (V : X.Opens) (hj : V ≤ C.cover j)
    (a : TwistedSections C n V) : Γ(X, V) :=
  res (le_inf le_rfl hj) (a.1 j)

@[simp] theorem toLocal_fromLocal (n : ℕ) (j : ι) (V : X.Opens)
    (hj : V ≤ C.cover j) (a : Γ(X, V)) :
    toLocal C n j V hj (fromLocal C n j V hj a) = a := by
  dsimp [toLocal, fromLocal]
  simp only [res_comp, C.self, Units.val_one,
    one_pow, one_mul, res_refl]

@[simp] theorem fromLocal_toLocal (n : ℕ) (j : ι) (V : X.Opens)
    (hj : V ≤ C.cover j) (a : TwistedSections C n V) :
    fromLocal C n j V hj (toLocal C n j V hj a) = a := by
  ext i
  dsimp [fromLocal, toLocal]
  rw [res_comp]
  exact (compatible_on C a i j (V ⊓ C.cover i) inf_le_left inf_le_right
    (inf_le_left.trans hj)).symm.trans (by rw [res_refl])

/-- Actual linear equivalence on every open in a trivializing chart. -/
def localLinearEquiv (n : ℕ) (j : ι) (V : X.Opens) (hj : V ≤ C.cover j) :
    TwistedSections C n V ≃ₗ[Γ(X, V)] Γ(X, V) where
  toFun := toLocal C n j V hj
  invFun := fromLocal C n j V hj
  left_inv := fromLocal_toLocal C n j V hj
  right_inv := toLocal_fromLocal C n j V hj
  map_add' a b := map_add _ _ _
  map_smul' r a := by
    change res _ (res inf_le_left r * a.1 j) = r * res _ (a.1 j)
    rw [map_mul, res_comp, res_refl]

/-- The local coordinates commute with all restrictions inside the chart. -/
theorem toLocal_restrict (n : ℕ) (j : ι) {V W : X.Opens}
    (h : V ≤ W) (hj : W ≤ C.cover j) (a : TwistedSections C n W) :
    toLocal C n j V (h.trans hj) (restrictSections C n h a) =
      res h (toLocal C n j W hj a) := by
  dsimp [toLocal]
  rw [res_comp, res_comp]

end ArithDyn.Extension.ProjTwist

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{max u v}} {ι : Type v} (C : UnitCocycle X ι)

/-- The actual restriction to any open in a chart is isomorphic to the unit module. -/
def localRestrictionIso (n : ℕ) (j : ι) (U : X.Opens) (hj : U ≤ C.cover j) :
    Scheme.Modules.restrict (twistedModule C n) U.ι ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V => ?_) ?_
  ·
    exact (ModuleCat.restrictScalarsId'App
      (((forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv).hom)
      (by simp only [Scheme.Opens.ι_appIso]; rfl) _) ≪≫
      (localLinearEquiv C n j (U.ι ''ᵁ V.unop)
        ((U.ι_image_le V.unop).trans hj)).toModuleIso
  · intro V W f
    ext a
    exact toLocal_restrict C n j (U.ι.image_mono f.unop.le)
      ((U.ι_image_le V.unop).trans hj) a

/-- In particular the actual inverse-image module along a chart is free of rank one. -/
def localPullbackIso (n : ℕ) (j : ι) (U : X.Opens) (hj : U ≤ C.cover j) :
    (Scheme.Modules.pullback U.ι).obj (twistedModule C n) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (twistedModule C n)).symm ≪≫
    localRestrictionIso C n j U hj

@[simp] theorem localRestrictionIso_hom_app (n : ℕ) (j : ι) (U : X.Opens)
    (hj : U ≤ C.cover j) (W : U.toScheme.Opens)
    (a : TwistedSections C n (U.ι ''ᵁ W)) :
    Scheme.Modules.Hom.app (localRestrictionIso C n j U hj).hom W a =
      toLocal C n j (U.ι ''ᵁ W) ((U.ι_image_le W).trans hj) a := rfl

@[simp] theorem localRestrictionIso_inv_app (n : ℕ) (j : ι) (U : X.Opens)
    (hj : U ≤ C.cover j) (W : U.toScheme.Opens) (a : Γ(X, U.ι ''ᵁ W)) :
    Scheme.Modules.Hom.app (localRestrictionIso C n j U hj).inv W a =
      fromLocal C n j (U.ι ''ᵁ W) ((U.ι_image_le W).trans hj) a := rfl

end ArithDyn.Extension.ProjTwist
