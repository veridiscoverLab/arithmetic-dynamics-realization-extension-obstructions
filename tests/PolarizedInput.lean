import ArithDyn.Extension.PolarizedSectionDynamics
import ArithDyn.Extension.SectionLifting

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
universe u v
open CategoryTheory AlgebraicGeometry MvPolynomial
open ArithDyn.Extension ArithDyn.Extension.ProjTwist ArithDyn.Extension.SectionAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

#print axioms sectionGradingOverBase_graded
#print axioms sectionEndOverBase
#print axioms polarizationAlgebraHom
#print axioms polarizationAlgebraHom_of
#print axioms polarizationAlgebraHom_mem
#print axioms polarizationAlgebraHom_degree_one
#print axioms polarizationAlgebraHom_restrict
#print axioms sectionAlgebraPullback_algebraMap
#print axioms polarizedAlgebraEnd
#print axioms polarizedAlgebraEnd_mem
#print axioms polarizedAlgebraEnd_algebraMap
#print axioms polarizedAlgebraEnd_degree_one
#print axioms polarizedAlgebraEnd_eq_power_sections
#print axioms polarizedAlgebraEndOverBase
#print axioms polarizedAlgebraEndOverBase_mem

-- A genuinely original Scheme universe with Fin 2 charts: no coefficient ULift.
example {k : Type u} [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (f : X ⟶ X) (hf : f ≫ p = p)
    (C : UnitCocycle X (Fin 2)) (d : ℕ)
    (e : (Scheme.Modules.pullback f).obj (twistedModule C 1) ≅ twistedModule C d) :
    letI := sectionBaseAlgebra p C
    sectionAlgebra C →ₐ[k] sectionAlgebra C :=
  polarizedAlgebraEndOverBase f C d e p hf

-- Instantiate the old lifting theorem with the constructed real ring/grading/dynamics.
-- The one required degree t*d restriction-surjectivity remains an honest premise.
example {k : Type u} [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (f : X ⟶ X) (hf : f ≫ p = p)
    (C : UnitCocycle X (Fin 2)) (d : ℕ)
    (e : (Scheme.Modules.pullback f).obj (twistedModule C 1) ≅ twistedModule C d)
    {r t : ℕ} (ht : 1 ≤ t) (coords : Fin (r + 1) → sectionAlgebra C) :
    letI := sectionBaseAlgebra p C
    ∀ (hcoords : ∀ i, coords i ∈ sectionGradingOverBase p C 1)
      (hres : ∀ x ∈ sectionGradingOverBase p C (t * d),
        ∃ q : MvPolynomial (Fin (r + 1)) k,
          q.IsHomogeneous (t * d) ∧ aeval coords q = x),
    let τ := polarizedAlgebraEndOverBase f C d e p hf
    let s : VerIdx r t → sectionAlgebra C :=
      fun α => aeval coords (verMon (k := k) r t α)
    let I := RingHom.ker (aeval s : MvPolynomial (VerIdx r t) k →ₐ[k] sectionAlgebra C)
    I.IsHomogeneous (homogeneousSubmodule (VerIdx r t) k) ∧
    ∃ F : VerIdx r t → MvPolynomial (VerIdx r t) k,
      (∀ α, (F α).IsHomogeneous d) ∧
      (∀ α, aeval s (F α) = τ (s α)) ∧
      (aeval s).comp (aeval F) = τ.comp (aeval s) ∧
      (∀ g ∈ I, aeval F g ∈ I) := by
  letI := sectionBaseAlgebra p C
  letI := sectionGradingOverBase_graded p C
  intro hcoords hres
  apply exists_polarized_lifts_with_homogeneous_kernel (sectionGradingOverBase p C)
    ht coords hcoords (polarizedAlgebraEndOverBase f C d e p hf) _ hres
  intro x hx
  simpa only [Nat.mul_comm d t] using
    polarizedAlgebraEndOverBase_mem f C d e p hf t x hx
