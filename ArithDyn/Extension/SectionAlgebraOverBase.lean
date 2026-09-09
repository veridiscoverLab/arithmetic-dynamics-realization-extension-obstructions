import ArithDyn.Extension.SectionAlgebraSheaf
import ArithDyn.Extension.SectionAlgebraMaps

/-!
# The original ground ring on the same complete section algebra

The structural morphism supplies the scalar map.  Restricting the already proved
internal grading preserves its carrier and all homogeneous decompositions.  The
regular functions are not identified with the ground ring.
-/

universe u v
open CategoryTheory AlgebraicGeometry
open ArithDyn.Extension.ProjTwist

namespace ArithDyn.Extension.SectionAlgebra
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) {ι : Type v} (C : UnitCocycle X ι)

/-- The original structural morphism acts on all global regular functions. -/
abbrev regularFunctionsBaseAlgebra : Algebra k Γ(X, ⊤) := (baseRingHom p).toAlgebra

/-- The original ground ring acts on the same section ring through regular functions. -/
abbrev sectionBaseAlgebra : Algebra k (sectionAlgebra C) :=
  ((algebraMap Γ(X, ⊤) (sectionAlgebra C)).comp (baseRingHom p)).toAlgebra

/-- The two explicit scalar maps form their actual scalar tower. -/
abbrev sectionBaseScalarTower :
    letI := regularFunctionsBaseAlgebra p
    letI := sectionBaseAlgebra p C
    IsScalarTower k Γ(X, ⊤) (sectionAlgebra C) := by
  letI := regularFunctionsBaseAlgebra p
  letI := sectionBaseAlgebra p C
  exact IsScalarTower.of_algebraMap_eq (R := k) (S := Γ(X, ⊤))
    (A := sectionAlgebra C) (fun _ => rfl)

/-- The original homogeneous pieces, with scalars restricted to the ground ring. -/
def sectionGradingOverBase :
    letI := sectionBaseAlgebra p C
    ℕ → Submodule k (sectionAlgebra C) := by
  letI := regularFunctionsBaseAlgebra p
  letI := sectionBaseAlgebra p C
  letI := sectionBaseScalarTower p C
  exact fun n => (sectionGradingOn C ⊤ n).restrictScalars k

/-- Restriction of scalars preserves the actual grading and decomposition. -/
abbrev sectionGradingOverBase_graded :
    letI := sectionBaseAlgebra p C
    GradedAlgebra (sectionGradingOverBase p C) := by
  letI := regularFunctionsBaseAlgebra p
  letI := sectionBaseAlgebra p C
  letI := sectionBaseScalarTower p C
  change GradedAlgebra (fun n => (sectionGradingOn C ⊤ n).restrictScalars k)
  infer_instance

/-- No homogeneous carrier changes when the original base is restored. -/
theorem sectionGradingOverBase_mem (n : ℕ) (a : sectionAlgebra C) :
    a ∈ sectionGradingOverBase p C n ↔ a ∈ sectionGradingOn C ⊤ n := Iff.rfl

/-- Exact recognition of a ring endomorphism over the original base; the stated
coefficient law is semilinearity over `Γ(X,O)`, not constancy of all its functions. -/
def sectionEndOverBase (f : X ⟶ X) (hf : f ≫ p = p)
    (τ : sectionAlgebra C →+* sectionAlgebra C)
    (hτ : ∀ r : Γ(X, ⊤), τ (algebraMap Γ(X, ⊤) (sectionAlgebra C) r) =
      algebraMap Γ(X, ⊤) (sectionAlgebra C) ((f.appTop).hom r)) :
    letI := sectionBaseAlgebra p C
    sectionAlgebra C →ₐ[k] sectionAlgebra C := by
  letI := sectionBaseAlgebra p C
  refine { τ with commutes' := ?_ }
  intro r
  change τ (algebraMap Γ(X, ⊤) (sectionAlgebra C) (baseRingHom p r)) =
    algebraMap Γ(X, ⊤) (sectionAlgebra C) (baseRingHom p r)
  rw [hτ]
  congr 1
  exact congrArg (fun g : k →+* Γ(X, ⊤) => g r)
    (baseRingHom_naturality f p p hf)

end
end ArithDyn.Extension.SectionAlgebra
