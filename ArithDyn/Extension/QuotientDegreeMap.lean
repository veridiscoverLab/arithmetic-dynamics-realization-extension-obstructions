import ArithDyn.Extension.GradedQuotient
import ArithDyn.Extension.DegreeMap
import ArithDyn.Extension.ProjRegrading

/-!
# Homogeneous coordinates on the Proj of the original quotient

This assembles the quotient grading, geometric base-point certificate and radical
Proj construction.  The domain is the actual Proj of `k[x]/I`, with the original
ideal. Both the intermediate weighted target and the final standard target are constructed.
The map is constructed from the given coordinates, not supplied as an input.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace ArithDyn.Extension

open MvPolynomial HomogeneousIdeal AlgebraicGeometry CategoryTheory GradedQuotient

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable {k : Type u} {σ ι : Type v} [Field k]

/-- The actual standard grading on the original homogeneous polynomial quotient. -/
abbrev polynomialQuotientGrading (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) :=
  component (homogeneousSubmodule σ k) (⟨I, hI⟩ : HomogeneousIdeal (homogeneousSubmodule σ k))

/-- This instance uses the proved quotient construction; it is not additional input data. -/
instance polynomialQuotientGradedAlgebra (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) :
    GradedAlgebra (polynomialQuotientGrading I hI) :=
  quotientGradedAlgebra (homogeneousSubmodule σ k)
    (⟨I, hI⟩ : HomogeneousIdeal (homogeneousSubmodule σ k))

/-- The given coordinate system, restricted to the original quotient, as a graded map. -/
noncomputable def quotientDegreeSubstitution (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d) :
    constantWeightGrading ι k d →+*ᵍ polynomialQuotientGrading I hI :=
  (quotientGradedMap (homogeneousSubmodule σ k) ⟨I, hI⟩).comp
    (degreeSubstitution d F hF)

/-- A radical certificate on the original zero locus descends to exactly the
irrelevant-ideal condition for the quotient's Proj map. -/
theorem quotient_irrelevant_le_radical_map (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (I ⊔ Ideal.span (Set.range F)).radical) :
    (irrelevant (polynomialQuotientGrading I hI)).toIdeal ≤
      (((irrelevant (constantWeightGrading ι k d)).map
        (quotientDegreeSubstitution I hI d F hF)).toIdeal).radical := by
  let q := quotientGradedMap (homogeneousSubmodule σ k)
    (⟨I, hI⟩ : HomogeneousIdeal (homogeneousSubmodule σ k))
  let J := ((irrelevant (constantWeightGrading ι k d)).map
    (quotientDegreeSubstitution I hI d F hF)).toIdeal
  have hIJ : I ⊔ Ideal.span (Set.range F) ≤ J.comap q := by
    apply sup_le
    · intro p hp
      change Ideal.Quotient.mk I p ∈ J
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
      exact J.zero_mem
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      have hi : X i ∈ (irrelevant (constantWeightGrading ι k d)).toIdeal :=
        mem_irrelevant_of_mem _ hd (isWeightedHomogeneous_X k (fun _ : ι => d) i)
      change q (F i) ∈ J
      have hmem : quotientDegreeSubstitution I hI d F hF (X i) ∈ J :=
        Ideal.mem_map_of_mem (quotientDegreeSubstitution I hI d F hF) hi
      simpa only [quotientDegreeSubstitution, GradedRingHom.comp_apply,
        degreeSubstitution_apply, aeval_X] using hmem
  have hpre : (irrelevant (homogeneousSubmodule σ k)).toIdeal ≤ J.radical.comap q := by
    rw [standard_irrelevant_eq_coordinateIdeal, Ideal.comap_radical]
    exact hbase.trans (Ideal.radical_mono hIJ)
  exact (toIdeal_le_toIdeal_iff.mpr
    (irrelevant_le_map_of_surjective q (quotientGradedMap_surjective _ _))).trans
    (Ideal.map_le_of_le_comap hpre)

/-- A genuine scheme morphism defined on the original, possibly nonreduced,
projective quotient by its given positive-degree coordinates. -/
noncomputable def quotientDegreeMapOfRadical (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (I ⊔ Ideal.span (Set.range F)).radical) :
    Proj (polynomialQuotientGrading I hI) ⟶ Proj (constantWeightGrading ι k d) :=
  Proj.mapRadical (quotientDegreeSubstitution I hI d F hF)
    (quotient_irrelevant_le_radical_map I hI d hd F hF hbase)

/-- Geometric base-point freeness suffices on the actual quotient, not just on its
reduced geometric point set. -/
noncomputable def quotientDegreeMap [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (F i) ≠ 0) :
    Proj (polynomialQuotientGrading I hI) ⟶ Proj (constantWeightGrading ι k d) :=
  quotientDegreeMapOfRadical I hI d hd F hF
    (coordinateIdeal_le_radical_of_no_basepoint I F hbase)

/-- The original quotient's coordinate morphism with a standard projective target.
The construction preserves the original quotient ring; no radical quotient is used. -/
def quotientStandardDegreeMapOfRadical (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (I ⊔ Ideal.span (Set.range F)).radical) :
    Proj (polynomialQuotientGrading I hI) ⟶ Proj (homogeneousSubmodule ι k) :=
  quotientDegreeMapOfRadical I hI d hd F hF hbase ≫ (constantWeightProjIso d hd).inv

/-- Geometric base-point freeness constructs the actual morphism from the original
projective quotient into standard projective space. Closed immersion of a particular
Veronese coordinate system and the twisting-sheaf comparison are separate statements. -/
def quotientStandardDegreeMap [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (F i) ≠ 0) :
    Proj (polynomialQuotientGrading I hI) ⟶ Proj (homogeneousSubmodule ι k) :=
  quotientStandardDegreeMapOfRadical I hI d hd F hF
    (coordinateIdeal_le_radical_of_no_basepoint I F hbase)

@[simp] theorem quotientStandardDegreeMap_preimage_basicOpen [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (d : ℕ) (hd : 0 < d) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (F i) ≠ 0)
    (p : MvPolynomial ι k) :
    quotientStandardDegreeMap I hI d hd F hF hbase ⁻¹ᵁ
        ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) p =
      ProjectiveSpectrum.basicOpen (polynomialQuotientGrading I hI)
        (Ideal.Quotient.mk I (aeval F p)) := rfl

end ArithDyn.Extension
