import ArithDyn.Extension.PolarizationAlgebra
import ArithDyn.Extension.ProjTwistPullbackMate
import ArithDyn.Extension.SectionAlgebraOverBase
import ArithDyn.Extension.PolarizationSheaf

/-!
# The complete section dynamics from the original scheme morphism and polarization

One actual pullback isomorphism supplies every degree of the same section-ring
endomorphism.  The degree-zero action is the actual pullback of regular functions;
when the original scheme morphism is over the ground ring, this is an algebra
endomorphism over that ground ring.
-/

universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace DirectSum
open ArithDyn.Extension.SectionAlgebra

namespace ArithDyn.Extension.ProjTwist
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 500000
noncomputable section

variable {X Y : Scheme.{max u v}} (f : X ⟶ Y) {ι : Type v} (C : UnitCocycle Y ι)

/-- Degree zero follows the actual map on the full regular-function ring. -/
theorem sectionAlgebraPullback_algebraMap (V : Y.Opens) (r : Γ(Y, V)) :
    sectionAlgebraPullback f C V (algebraMap Γ(Y, V) (sectionAlgebraOn C V) r) =
      algebraMap Γ(X, f ⁻¹ᵁ V) (sectionAlgebraOn (pullbackCocycle f C) (f ⁻¹ᵁ V))
        ((f.app V).hom r) := by
  rw [DirectSum.algebraMap_apply, sectionAlgebraPullback_of, DirectSum.algebraMap_apply]
  congr 1
  ext i
  change pullRegular f le_rfl (res inf_le_left r) =
    res (f.preimage_mono (inf_le_left : V ⊓ C.cover i ≤ V)) ((f.app V).hom r)
  rw [pullRegular_res, ← Scheme.Hom.appLE_eq_app f, res_pullRegular]

end
noncomputable section
variable {X : Scheme.{max u v}} (f : X ⟶ X) {ι : Type v} (C : UnitCocycle X ι) (d : ℕ)
variable (e : (Scheme.Modules.pullback f).obj (twistedModule C 1) ≅ twistedModule C d)

/-- Express the original polarization in the canonically pulled local frames. -/
def polarizationFromPullback :
    twistedModule (pullbackCocycle f C) 1 ≅ twistedModule C d :=
  (pullbackTwistedIso f C 1).symm ≪≫ e

@[simp] theorem polarizationFromPullback_comp :
    pullbackComparison f C 1 ≫ (polarizationFromPullback f C d e).hom = e.hom := by
  change (pullbackTwistedIso f C 1).hom ≫ (pullbackTwistedIso f C 1).inv ≫ e.hom = e.hom
  exact Iso.hom_inv_id_assoc _ _

/-- The actual morphism and its one polarization act on the entire section ring. -/
def polarizedAlgebraEnd : sectionAlgebra C →+* sectionAlgebra C :=
  (polarizationAlgebraHom (pullbackCocycle f C) C d
    (polarizationFromPullback f C d e) ⊤).toRingHom.comp (sectionAlgebraPullback f C ⊤)

/-- Every degree belongs to this same endomorphism. -/
@[simp] theorem polarizedAlgebraEnd_of (n : ℕ) (a : TwistedSections C n ⊤) :
    polarizedAlgebraEnd f C d e (DirectSum.of (fun n => ↥(TwistedSections C n ⊤)) n a) =
      DirectSum.of (fun n => ↥(TwistedSections C n ⊤)) (d * n)
        (globalPowerSections (pullbackCocycle f C) C d (polarizationFromPullback f C d e)
          n ⊤ (pullbackSections f C n ⊤ a)) := by
  change polarizationAlgebraHom (pullbackCocycle f C) C d
    (polarizationFromPullback f C d e) ⊤ (sectionAlgebraPullback f C ⊤ _) = _
  rw [sectionAlgebraPullback_of]
  exact polarizationAlgebraHom_of (pullbackCocycle f C) C d
    (polarizationFromPullback f C d e) ⊤ n (pullbackSections f C n ⊤ a)

/-- Degree scaling uses the original internal grading, without replacing the ring. -/
theorem polarizedAlgebraEnd_mem (n : ℕ) (a : sectionAlgebra C)
    (ha : a ∈ sectionGradingOn C ⊤ n) :
    polarizedAlgebraEnd f C d e a ∈ sectionGradingOn C ⊤ (d * n) := by
  obtain ⟨b, rfl⟩ := ha
  rw [show DirectSum.lof Γ(X, ⊤) ℕ (fun n => ↥(TwistedSections C n ⊤)) n b =
    DirectSum.of (fun n => ↥(TwistedSections C n ⊤)) n b from rfl, polarizedAlgebraEnd_of]
  exact sectionInclusion_mem C ⊤ (d * n) _

/-- All regular functions undergo the original pullback; they need not be constants. -/
theorem polarizedAlgebraEnd_algebraMap (r : Γ(X, ⊤)) :
    polarizedAlgebraEnd f C d e (algebraMap Γ(X, ⊤) (sectionAlgebra C) r) =
      algebraMap Γ(X, ⊤) (sectionAlgebra C) (f.appTop.hom r) := by
  change polarizationAlgebraHom (pullbackCocycle f C) C d
    (polarizationFromPullback f C d e) ⊤ (sectionAlgebraPullback f C ⊤ _) = _
  rw [sectionAlgebraPullback_algebraMap]
  exact (polarizationAlgebraHom (pullbackCocycle f C) C d
    (polarizationFromPullback f C d e) ⊤).commutes (f.appTop.hom r)

/-- On degree one the whole ring map is the original polarization's adjoint. -/
theorem polarizedAlgebraEnd_degree_one (a : TwistedSections C 1 ⊤) :
    polarizedAlgebraEnd f C d e (DirectSum.of (fun n => ↥(TwistedSections C n ⊤)) 1 a) =
      DirectSum.of (fun n => ↥(TwistedSections C n ⊤)) d
        (polarizedOnSections f e ⊤ a) := by
  change polarizationAlgebraHom (pullbackCocycle f C) C d
    (polarizationFromPullback f C d e) ⊤ (sectionAlgebraPullback f C ⊤ _) = _
  rw [sectionAlgebraPullback_of]
  erw [polarizationAlgebraHom_degree_one]
  congr 1
  change Scheme.Modules.Hom.app (polarizationFromPullback f C d e).hom ⊤
    (pullbackSections f C 1 ⊤ a) = mapOnSections f e.hom ⊤ a
  rw [← polarizationFromPullback_comp f C d e, mapOnSections_comp]
  congr 1
  change pullbackSections f C 1 ⊤ a =
    Scheme.Modules.Hom.app (adjoint f (pullbackComparison f C 1)) ⊤ a
  rw [adjoint, pullbackComparison_adjoint]
  rfl

/-- The ring construction uses exactly the same transported polarization as
all actual sheaf-power isomorphisms. -/
theorem polarizationFromPullback_eq :
    polarizationFromPullback f C d e = polarizationCocycleIso f C d e := rfl

/-- Every homogeneous summand is the adjoint of the actual sheaf-power
isomorphism derived from the single original polarization. -/
theorem polarizedAlgebraEnd_eq_power_sections (n : ℕ) (a : TwistedSections C n ⊤) :
    polarizedAlgebraEnd f C d e (DirectSum.of (fun n => ↥(TwistedSections C n ⊤)) n a) =
      DirectSum.of (fun n => ↥(TwistedSections C n ⊤)) (d * n)
        (polarizedOnSections f (polarizationPowerIso f C d e n) ⊤ a) := by
  rw [polarizedAlgebraEnd_of]
  congr 1
  change globalPowerSections (pullbackCocycle f C) C d (polarizationFromPullback f C d e)
    n ⊤ (pullbackSections f C n ⊤ a) =
      mapOnSections f (pullbackComparison f C n ≫
        globalPowerModuleHom (pullbackCocycle f C) C d (polarizationCocycleIso f C d e) n) ⊤ a
  rw [mapOnSections_comp, pullbackComparison_onSections]
  rfl

section Base
variable {k : Type (max u v)} [CommRing k]
  (p : X ⟶ Spec (CommRingCat.of k)) (hf : f ≫ p = p)

/-- The single original polarization gives a genuine endomorphism over the
original base ring, with its actual structural morphism equation. -/
def polarizedAlgebraEndOverBase :
    letI := sectionBaseAlgebra p C
    sectionAlgebra C →ₐ[k] sectionAlgebra C :=
  sectionEndOverBase p C f hf (polarizedAlgebraEnd f C d e)
    (polarizedAlgebraEnd_algebraMap f C d e)

/-- Restricting scalars keeps the same degree-scaling law. -/
theorem polarizedAlgebraEndOverBase_mem (n : ℕ) (a : sectionAlgebra C)
    (ha : a ∈ sectionGradingOverBase p C n) :
    polarizedAlgebraEndOverBase f C d e p hf a ∈ sectionGradingOverBase p C (d * n) :=
  polarizedAlgebraEnd_mem f C d e n a ha

end Base
end
end ArithDyn.Extension.ProjTwist
