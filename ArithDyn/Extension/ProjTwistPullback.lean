import ArithDyn.Extension.ProjTwistPullbackLocal
import ArithDyn.Extension.SectionAlgebraPullback
import ArithDyn.Extension.SectionAlgebraMaps

/-!
# The canonical actual pullback comparison

The comparison is the adjoint of the coefficientwise map of the same cocycle.
The formulas below control its adjoint on every open and every twist degree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace

namespace ArithDyn.Extension.ProjTwist

variable {X Y : Scheme.{max u v}} (f : X ⟶ Y) {ι : Type v} (C : UnitCocycle Y ι)

/-- The actual adjoint comparison, without assuming that it is an isomorphism. -/
def pullbackComparison (n : ℕ) :
    (Modules.pullback f).obj (twistedModule C n) ⟶
      twistedModule (pullbackCocycle f C) n :=
  ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (pullbackSectionsHom f C n)

@[simp] theorem pullbackComparison_adjoint (n : ℕ) :
    (Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackComparison f C n) =
      pullbackSectionsHom f C n :=
  Equiv.apply_symm_apply _ _

/-- The comparison induces exactly the original coefficientwise map. -/
@[simp] theorem pullbackComparison_onSections (n : ℕ) (V : Y.Opens)
    (a : TwistedSections C n V) :
    SectionAlgebra.mapOnSections f (pullbackComparison f C n) V a =
      pullbackSections f C n V a := by
  exact congrArg (fun h : (twistedModule C n : Y.Modules) ⟶
      (Modules.pushforward f).obj (twistedModule (pullbackCocycle f C) n) =>
    Modules.Hom.app h V a) (pullbackComparison_adjoint f C n)

/-- In each actual chart basis the adjoint map is exactly pullback of regular functions. -/
theorem pullbackSections_toLocal (n : ℕ) (j : ι) (V : Y.Opens)
    (hj : V ≤ C.cover j) (a : TwistedSections C n V) :
    toLocal (pullbackCocycle f C) n j (f ⁻¹ᵁ V) (f.preimage_mono hj)
      (pullbackSections f C n V a) =
      pullRegular f le_rfl (toLocal C n j V hj a) := by
  change res (f.preimage_mono (le_inf le_rfl hj)) (pullRegular f le_rfl (a.1 j)) =
    pullRegular f le_rfl (res (le_inf le_rfl hj) (a.1 j))
  exact (res_pullRegular f (f.preimage_mono (le_inf le_rfl hj)) le_rfl (a.1 j)).trans
    (pullRegular_res f (le_inf le_rfl hj) le_rfl (a.1 j)).symm

/-- The single chart generator and all its scalar multiples pull back to the same generator. -/
theorem pullbackSections_fromLocal (n : ℕ) (j : ι) (V : Y.Opens)
    (hj : V ≤ C.cover j) (a : Γ(Y, V)) :
    pullbackSections f C n V (fromLocal C n j V hj a) =
      fromLocal (pullbackCocycle f C) n j (f ⁻¹ᵁ V) (f.preimage_mono hj)
        (pullRegular f le_rfl a) := by
  apply (localLinearEquiv (pullbackCocycle f C) n j (f ⁻¹ᵁ V)
    (f.preimage_mono hj)).injective
  change toLocal (pullbackCocycle f C) n j (f ⁻¹ᵁ V) (f.preimage_mono hj) _ =
    toLocal (pullbackCocycle f C) n j (f ⁻¹ᵁ V) (f.preimage_mono hj) _
  rw [pullbackSections_toLocal f C n j V hj, toLocal_fromLocal,
    toLocal_fromLocal]

/-- All local basis generators are preserved, on every degree simultaneously. -/
theorem pullbackSections_basis (n : ℕ) (j : ι) :
    pullbackSections f C n (C.cover j) (fromLocal C n j (C.cover j) le_rfl 1) =
      fromLocal (pullbackCocycle f C) n j (f ⁻¹ᵁ C.cover j) le_rfl 1 := by
  rw [pullbackSections_fromLocal, map_one]

/-- The actual local matrix of the canonical comparison in the constructed bases. -/
def comparisonLocalMatrix (n : ℕ) (i : ι) :
    SheafOfModules.unit (f ⁻¹ᵁ C.cover i).toScheme.ringCatSheaf ⟶
      SheafOfModules.unit (f ⁻¹ᵁ C.cover i).toScheme.ringCatSheaf :=
  (inverseImageRestrictionIso f C n i).inv ≫
    (Modules.restrictFunctor (f ⁻¹ᵁ C.cover i).ι).map (pullbackComparison f C n) ≫
      (localRestrictionIso (pullbackCocycle f C) n i (f ⁻¹ᵁ C.cover i) le_rfl).hom

/-- The single global comparison is invertible exactly when all its actual local
matrices are invertible.  Local freeness alone is not substituted for this condition. -/
theorem pullbackComparison_isIso_iff (n : ℕ) :
    IsIso (pullbackComparison f C n) ↔ ∀ i, IsIso (comparisonLocalMatrix f C n i) := by
  constructor
  · intro h i
    letI := h
    unfold comparisonLocalMatrix
    infer_instance
  · intro h
    apply isIso_of_restrictions (fun i => f ⁻¹ᵁ C.cover i)
      (f.iSup_preimage_eq_top C.covers) (pullbackComparison f C n)
    intro i
    have hi := h i
    simpa only [comparisonLocalMatrix, isIso_comp_left_iff,
      isIso_comp_right_iff] using hi

end ArithDyn.Extension.ProjTwist
