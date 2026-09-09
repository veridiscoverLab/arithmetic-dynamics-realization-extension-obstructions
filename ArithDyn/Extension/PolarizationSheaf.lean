import ArithDyn.Extension.PolarizationGluing
import ArithDyn.Extension.ProjTwistLocalIso
import ArithDyn.Extension.ProjTwistPullbackMate

/-!
# Actual sheaf isomorphisms in all powers of one polarization

The maps of all degrees are derived from a single original isomorphism.  Their
local matrices are the corresponding powers of its actual transition units.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace Opposite

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{max u v}} {ι : Type v} (C D : UnitCocycle X ι) (d : ℕ)
variable (μ : twistedModule C 1 ≅ twistedModule D d)

/-- The constructed degree map is a morphism of the actual module sheaves. -/
def globalPowerModuleHom (n : ℕ) :
    (twistedModule C n : X.Modules) ⟶ twistedModule D (d * n) where
  val := PresheafOfModules.homMk {
    app := fun V => AddCommGrpCat.ofHom (globalPowerLinearMap C D d μ n V.unop).toAddMonoidHom
    naturality := fun {V W} h => by
      ext a
      exact globalPowerSections_restrict C D d μ n h.unop.le a }
    (fun V r a => globalPowerSections_smul C D d μ n V.unop r a)

@[simp] theorem globalPowerModuleHom_app (n : ℕ) (V : X.Opens)
    (a : TwistedSections C n V) :
    Modules.Hom.app (globalPowerModuleHom C D d μ n) V a =
      globalPowerSections C D d μ n V a := rfl

/-- In each pair of actual frames the map is multiplication by a unit power. -/
def powerLocalLinearEquiv (n : ℕ) (i j : ι) (V : X.Opens)
    (hi : V ≤ C.cover i) (hj : V ≤ D.cover j) :
    TwistedSections C n V ≃ₗ[Γ(X, V)] TwistedSections D (d * n) V :=
  (localLinearEquiv C n i V hi).trans
    ((LinearEquiv.smulOfUnit (polarizationUnit C D d μ i j V hi hj ^ n)).trans
      (localLinearEquiv D (d * n) j V hj).symm)

theorem globalPowerSections_eq_local (n : ℕ) (i j : ι) (V : X.Opens)
    (hi : V ≤ C.cover i) (hj : V ≤ D.cover j) (a : TwistedSections C n V) :
    globalPowerSections C D d μ n V a = powerLocalLinearEquiv C D d μ n i j V hi hj a := by
  apply (localLinearEquiv D (d * n) j V hj).injective
  change toLocal D (d * n) j V hj (globalPowerSections C D d μ n V a) =
    toLocal D (d * n) j V hj
      (fromLocal D (d * n) j V hj
        ((polarizationUnit C D d μ i j V hi hj : Γ(X, V)) ^ n * toLocal C n i V hi a))
  rw [toLocal_fromLocal]
  have h := globalPowerSections_coefficient C D d μ n V a i j V le_rfl hi hj
  simpa only [crossPowerCoefficient, chartCoefficient, restrictSections_refl, toLocal] using h

/-- All section maps on any open in a common source/target chart are bijections. -/
theorem globalPowerSections_local_bijective (n : ℕ) (i j : ι) (V : X.Opens)
    (hi : V ≤ C.cover i) (hj : V ≤ D.cover j) :
    Function.Bijective (globalPowerSections C D d μ n V) := by
  have he : globalPowerSections C D d μ n V =
      fun a => (powerLocalLinearEquiv C D d μ n i j V hi hj).toFun a :=
    funext (globalPowerSections_eq_local C D d μ n i j V hi hj)
  rw [he]
  exact LinearEquiv.bijective _

/-- The actual module map is an isomorphism on the full common refinement. -/
instance globalPowerModuleHom_isIso (n : ℕ) : IsIso (globalPowerModuleHom C D d μ n) := by
  apply isIso_of_restrictions (fun ij : ι × ι => C.cover ij.1 ⊓ D.cover ij.2)
  · rw [iSup_prod]
    simp only [← inf_iSup_eq, D.covers, inf_top_eq, C.covers]
  · intro ij
    let U := C.cover ij.1 ⊓ D.cover ij.2
    apply (isIso_iff_of_reflects_iso _ (Modules.toPresheaf U.toScheme)).mp
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro W
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (globalPowerSections C D d μ n (U.ι ''ᵁ W.unop))
    exact globalPowerSections_local_bijective C D d μ n ij.1 ij.2 _
      ((U.ι_image_le W.unop).trans inf_le_left) ((U.ι_image_le W.unop).trans inf_le_right)

/-- All actual twist-sheaf isomorphisms are derived from the one original polarization. -/
def globalPowerModuleIso (n : ℕ) :
    (twistedModule C n : X.Modules) ≅ twistedModule D (d * n) :=
  asIso (globalPowerModuleHom C D d μ n)

@[simp] theorem globalPowerModuleIso_hom (n : ℕ) :
    (globalPowerModuleIso C D d μ n).hom = globalPowerModuleHom C D d μ n := rfl

end ArithDyn.Extension.ProjTwist

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{max u v}} {ι : Type v} (f : X ⟶ X) (C : UnitCocycle X ι) (d : ℕ)
variable (e : (Modules.pullback f).obj (twistedModule C 1) ≅ twistedModule C d)

/-- One original polarization, transported through the canonical actual
inverse-image comparison. -/
def polarizationCocycleIso :
    twistedModule (pullbackCocycle f C) 1 ≅ twistedModule C d :=
  (pullbackTwistedIso f C 1).symm ≪≫ e

/-- The actual pullback isomorphisms in all degrees follow from the single
original degree-one polarization, with no family of higher maps as input. -/
def polarizationPowerIso (n : ℕ) :
    (Modules.pullback f).obj (twistedModule C n) ≅ twistedModule C (d * n) :=
  pullbackTwistedIso f C n ≪≫
    globalPowerModuleIso (pullbackCocycle f C) C d (polarizationCocycleIso f C d e) n

end ArithDyn.Extension.ProjTwist
