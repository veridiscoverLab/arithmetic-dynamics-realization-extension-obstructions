import ArithDyn.Extension.PolarizationGluing
import ArithDyn.Extension.SectionAlgebraSheaf

/-!
# A complete section-algebra map from one actual polarization

The only polarization datum is the original isomorphism `μ`.  Every degree map
uses its extracted units and their powers; no independent family of dynamics is
an input.  No cover refinement is assumed.
-/

universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace DirectSum
open ArithDyn.Extension.SectionAlgebra

namespace ArithDyn.Extension.ProjTwist
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

variable {X : Scheme.{max u v}} {ι : Type v} (C D : UnitCocycle X ι) (d : ℕ)
variable (μ : twistedModule C 1 ≅ twistedModule D d)

/-- Equality of degrees and all original chart coefficients gives equality
inside the one direct sum. -/
theorem sectionOf_eq_of_coefficients {V : X.Opens} {n m : ℕ} (h : n = m)
    (a : TwistedSections D n V) (b : TwistedSections D m V)
    (hab : ∀ i, a.1 i = b.1 i) :
    DirectSum.of (fun n => ↥(TwistedSections D n V)) n a =
      DirectSum.of (fun n => ↥(TwistedSections D n V)) m b := by
  subst m
  congr 1
  ext i
  exact hab i

/-- All degrees of one original isomorphism form a genuine algebra homomorphism
on the complete actual section algebra.  The scalar ring is all regular functions. -/
def polarizationAlgebraHom (V : X.Opens) :
    sectionAlgebraOn C V →ₐ[Γ(X, V)] sectionAlgebraOn D V :=
  DirectSum.toAlgebra Γ(X, V) (fun n => ↥(TwistedSections C n V))
    (fun n => (DirectSum.lof Γ(X, V) ℕ (fun n => ↥(TwistedSections D n V)) (d * n)).comp
      (globalPowerLinearMap C D d μ n V))
    (by
      change DirectSum.of (fun n => ↥(TwistedSections D n V)) (d * 0)
        (globalPowerSections C D d μ 0 V ⟨1, compatible_one C V⟩) =
          DirectSum.of (fun n => ↥(TwistedSections D n V)) 0 ⟨1, compatible_one D V⟩
      exact sectionOf_eq_of_coefficients D (Nat.mul_zero d) _ _
        (globalPowerSections_zero_one_apply C D d μ V))
    (by
      intro n m a b
      change DirectSum.of (fun n => ↥(TwistedSections D n V)) (d * (n + m))
        (globalPowerSections C D d μ (n + m) V (mulSections C a b)) =
          DirectSum.of (fun n => ↥(TwistedSections D n V)) (d * n)
            (globalPowerSections C D d μ n V a) *
          DirectSum.of (fun n => ↥(TwistedSections D n V)) (d * m)
            (globalPowerSections C D d μ m V b)
      rw [DirectSum.of_mul_of]
      exact sectionOf_eq_of_coefficients D (Nat.mul_add d n m) _ _
        (globalPowerSections_mul_apply C D d μ a b))

@[simp] theorem polarizationAlgebraHom_of (V : X.Opens) (n : ℕ)
    (a : TwistedSections C n V) :
    polarizationAlgebraHom C D d μ V
      (DirectSum.of (fun n => ↥(TwistedSections C n V)) n a) =
        DirectSum.of (fun n => ↥(TwistedSections D n V)) (d * n)
          (globalPowerSections C D d μ n V a) := by
  simp only [polarizationAlgebraHom, DirectSum.toAlgebra_apply, DirectSum.toSemiring_of]
  rfl

/-- The one map scales the actual internal grading by the original degree. -/
theorem polarizationAlgebraHom_mem (V : X.Opens) (n : ℕ)
    (a : sectionAlgebraOn C V) (ha : a ∈ sectionGradingOn C V n) :
    polarizationAlgebraHom C D d μ V a ∈ sectionGradingOn D V (d * n) := by
  obtain ⟨b, rfl⟩ := ha
  rw [show DirectSum.lof Γ(X, V) ℕ (fun n => ↥(TwistedSections C n V)) n b =
    DirectSum.of (fun n => ↥(TwistedSections C n V)) n b from rfl,
    polarizationAlgebraHom_of]
  exact sectionInclusion_mem D V (d * n) _

/-- Degree one is the originally supplied module-sheaf isomorphism. -/
theorem polarizationAlgebraHom_degree_one (V : X.Opens) (a : TwistedSections C 1 V) :
    polarizationAlgebraHom C D d μ V
      (DirectSum.of (fun n => ↥(TwistedSections C n V)) 1 a) =
        DirectSum.of (fun n => ↥(TwistedSections D n V)) d
          (polarizationSectionEquiv C D d μ V a) := by
  rw [polarizationAlgebraHom_of]
  exact sectionOf_eq_of_coefficients D (Nat.mul_one d) _ _
    (globalPowerSections_one_apply C D d μ V a)

/-- The full algebra map commutes with every restriction on the original scheme. -/
theorem polarizationAlgebraHom_restrict {V W : X.Opens} (h : V ≤ W) :
    (polarizationAlgebraHom C D d μ V).toRingHom.comp (sectionRestriction C h) =
      (sectionRestriction D h).comp (polarizationAlgebraHom C D d μ W).toRingHom := by
  apply DirectSum.ringHom_ext
  intro n a
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    sectionRestriction_of, polarizationAlgebraHom_of, globalPowerSections_restrict]

end
end ArithDyn.Extension.ProjTwist
