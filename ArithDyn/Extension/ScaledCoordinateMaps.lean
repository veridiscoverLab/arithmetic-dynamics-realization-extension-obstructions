import ArithDyn.Extension.ScaledProjMap
import ArithDyn.Extension.QuotientDynamics
import ArithDyn.Extension.QuotientDegreeMap

/-!
# The original coordinate maps as degree-scaled homogeneous maps

This file bundles the original polynomial substitution, its restriction to the
original ideal quotient, and the quotient endomorphism induced by preservation of
that ideal.  Their degree conditions and irrelevant-ideal certificates are proved
from the coordinate hypotheses.  No projective morphism is assumed as input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

namespace ArithDyn.Extension

open MvPolynomial HomogeneousIdeal GradedQuotient

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable {k : Type u} {σ ι : Type v} [Field k]

/-- The original coordinate substitution with its actual degree multiplication. -/
def aevalDegreeScaledHom (d : ℕ) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d) :
    DegreeScaledHom (homogeneousSubmodule ι k) (homogeneousSubmodule σ k) d :=
  ⟨(aeval F).toRingHom, fun n p hp => (mem_homogeneousSubmodule _ _).mpr
    (((mem_homogeneousSubmodule n p).mp hp).aeval F hF)⟩

@[simp] theorem aevalDegreeScaledHom_apply (d : ℕ) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d) (p : MvPolynomial ι k) :
    (aevalDegreeScaledHom d F hF).1 p = aeval F p := rfl

/-- The coordinate map into the original quotient, with its degree scaling. -/
def quotientCoordinatesDegreeScaledHom (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d) :
    DegreeScaledHom (homogeneousSubmodule ι k) (polynomialQuotientGrading I hI) d :=
  ⟨(quotientCoordinates I F).toRingHom, fun n p hp =>
    mk_mem_component (homogeneousSubmodule σ k) ⟨I, hI⟩
      ((mem_homogeneousSubmodule _ _).mpr
        (((mem_homogeneousSubmodule n p).mp hp).aeval F hF))⟩

@[simp] theorem quotientCoordinatesDegreeScaledHom_apply (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (p : MvPolynomial ι k) :
    (quotientCoordinatesDegreeScaledHom I hI d F hF).1 p =
      Ideal.Quotient.mk I (aeval F p) := rfl

/-- Preservation of the original ideal defines the quotient endomorphism; its
degree multiplication follows on every original quotient component. -/
def quotientEndDegreeScaledHom (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ)
    (f : σ → MvPolynomial σ k) (hf : ∀ i, (f i).IsHomogeneous d)
    (hpres : ∀ g ∈ I, aeval f g ∈ I) :
    DegreeScaledHom (polynomialQuotientGrading I hI) (polynomialQuotientGrading I hI) d :=
  ⟨(quotientEnd I f hpres).toRingHom, fun n x hx => by
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hx
    exact mk_mem_component (homogeneousSubmodule σ k) ⟨I, hI⟩
      ((mem_homogeneousSubmodule _ _).mpr
        (((mem_homogeneousSubmodule _ _).mp hg).aeval f hf))⟩

@[simp] theorem quotientEndDegreeScaledHom_mk (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ)
    (f : σ → MvPolynomial σ k) (hf : ∀ i, (f i).IsHomogeneous d)
    (hpres : ∀ g ∈ I, aeval f g ∈ I) (g : MvPolynomial σ k) :
    (quotientEndDegreeScaledHom I hI d f hf hpres).1 (Ideal.Quotient.mk I g) =
      Ideal.Quotient.mk I (aeval f g) := rfl

/-- The polynomial radical certificate supplies the irrelevant-ideal condition
for the same substitution between standard gradings. -/
theorem aevalDegreeScaledHom_irrelevant (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (Ideal.span (Set.range F)).radical) :
    (irrelevant (homogeneousSubmodule σ k)).toIdeal ≤
      ((irrelevant (homogeneousSubmodule ι k)).toIdeal.map
        (aevalDegreeScaledHom d F hF).1).radical := by
  simpa only [HomogeneousIdeal.toIdeal_map, constantWeight_irrelevant_eq d hd] using
    irrelevant_le_radical_map_degreeSubstitution d hd F hF hbase

/-- The certificate on the original zero locus supplies the required irrelevant
containment for the original quotient coordinate map. -/
theorem quotientCoordinatesDegreeScaledHom_irrelevant
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (I ⊔ Ideal.span (Set.range F)).radical) :
    (irrelevant (polynomialQuotientGrading I hI)).toIdeal ≤
      ((irrelevant (homogeneousSubmodule ι k)).toIdeal.map
        (quotientCoordinatesDegreeScaledHom I hI d F hF).1).radical := by
  simpa only [HomogeneousIdeal.toIdeal_map, constantWeight_irrelevant_eq d hd] using
    quotient_irrelevant_le_radical_map I hI d hd F hF hbase

/-- The original quotient self-map satisfies the irrelevant-ideal condition.
The proof keeps its original ideal-preservation hypothesis and factors the
coordinate images through that very quotient endomorphism. -/
theorem quotientEndDegreeScaledHom_irrelevant (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (f : σ → MvPolynomial σ k) (hf : ∀ i, (f i).IsHomogeneous d)
    (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (I ⊔ Ideal.span (Set.range f)).radical) :
    (irrelevant (polynomialQuotientGrading I hI)).toIdeal ≤
      ((irrelevant (polynomialQuotientGrading I hI)).toIdeal.map
        (quotientEndDegreeScaledHom I hI d f hf hpres).1).radical := by
  apply (quotientCoordinatesDegreeScaledHom_irrelevant I hI d hd f hf hbase).trans
  apply Ideal.radical_mono
  rw [Ideal.map_le_iff_le_comap, standard_irrelevant_eq_coordinateIdeal]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have hi : Ideal.Quotient.mk I (X i) ∈
      (irrelevant (polynomialQuotientGrading I hI)).toIdeal :=
    mem_irrelevant_of_mem _ (by omega : 0 < (1 : ℕ))
      (mk_mem_component (homogeneousSubmodule σ k) ⟨I, hI⟩ (isHomogeneous_X k i))
  have hm := Ideal.mem_map_of_mem (quotientEndDegreeScaledHom I hI d f hf hpres).1 hi
  change Ideal.Quotient.mk I (aeval f (X i)) ∈
    (irrelevant (polynomialQuotientGrading I hI)).toIdeal.map
      (quotientEndDegreeScaledHom I hI d f hf hpres).1
  simpa only [quotientEndDegreeScaledHom_mk, aeval_X] using hm

/-- Geometric base-point freeness gives the certificate for the polynomial map. -/
theorem aevalDegreeScaledHom_irrelevant_of_no_basepoint [Finite σ]
    (d : ℕ) (hd : 0 < d) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0) :
    (irrelevant (homogeneousSubmodule σ k)).toIdeal ≤
      ((irrelevant (homogeneousSubmodule ι k)).toIdeal.map
        (aevalDegreeScaledHom d F hF).1).radical :=
  aevalDegreeScaledHom_irrelevant d hd F hF
    (coordinateIdeal_le_radical_of_global_no_basepoint F hbase)

/-- Geometric base-point freeness on the original ideal quotient gives the
certificate for its coordinate map. -/
theorem quotientCoordinatesDegreeScaledHom_irrelevant_of_no_basepoint [Finite σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (F i) ≠ 0) :
    (irrelevant (polynomialQuotientGrading I hI)).toIdeal ≤
      ((irrelevant (homogeneousSubmodule ι k)).toIdeal.map
        (quotientCoordinatesDegreeScaledHom I hI d F hF).1).radical :=
  quotientCoordinatesDegreeScaledHom_irrelevant I hI d hd F hF
    (coordinateIdeal_le_radical_of_no_basepoint I F hbase)

/-- Geometric base-point freeness and preservation of the original ideal give
the certificate for the quotient self-map. -/
theorem quotientEndDegreeScaledHom_irrelevant_of_no_basepoint [Finite σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (f : σ → MvPolynomial σ k) (hf : ∀ i, (f i).IsHomogeneous d)
    (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (f i) ≠ 0) :
    (irrelevant (polynomialQuotientGrading I hI)).toIdeal ≤
      ((irrelevant (polynomialQuotientGrading I hI)).toIdeal.map
        (quotientEndDegreeScaledHom I hI d f hf hpres).1).radical :=
  quotientEndDegreeScaledHom_irrelevant I hI d hd f hf hpres
    (coordinateIdeal_le_radical_of_no_basepoint I f hbase)

/-- The scaled input maps retain the exact original quotient-algebra square. -/
theorem degreeScaledCoordinateMaps_commuting_square (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (s d : ℕ)
    (j : ι → MvPolynomial σ k) (hj : ∀ i, (j i).IsHomogeneous s)
    (Ψ : ι → MvPolynomial ι k) (hΨ : ∀ i, (Ψ i).IsHomogeneous d)
    (f : σ → MvPolynomial σ k) (hf : ∀ i, (f i).IsHomogeneous d)
    (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hcomm : ∀ i, aeval j (Ψ i) - aeval f (j i) ∈ I) :
    (quotientCoordinatesDegreeScaledHom I hI s j hj).1.comp (aevalDegreeScaledHom d Ψ hΨ).1 =
      (quotientEndDegreeScaledHom I hI d f hf hpres).1.comp
        (quotientCoordinatesDegreeScaledHom I hI s j hj).1 :=
  congrArg AlgHom.toRingHom (quotient_commuting_square I j Ψ f hpres hcomm)

open AlgebraicGeometry CategoryTheory

/-- The actual Proj morphism of the given globally base-point-free polynomial
coordinate system, using standard gradings on both sides. -/
def scaledPolynomialProjMap [Finite σ] (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0) :
    Proj (homogeneousSubmodule σ k) ⟶ Proj (homogeneousSubmodule ι k) :=
  DegreeScaledHom.projMap (aevalDegreeScaledHom d F hF) hd
    (aevalDegreeScaledHom_irrelevant_of_no_basepoint d hd F hF hbase)

/-- The actual Proj coordinate map from the original ideal quotient. -/
def scaledQuotientCoordinateProjMap [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (F i) ≠ 0) :
    Proj (polynomialQuotientGrading I hI) ⟶ Proj (homogeneousSubmodule ι k) :=
  DegreeScaledHom.projMap (quotientCoordinatesDegreeScaledHom I hI d F hF) hd
    (quotientCoordinatesDegreeScaledHom_irrelevant_of_no_basepoint I hI d hd F hF hbase)

/-- The actual self-morphism of the original projective quotient, induced by
the same ideal-preserving polynomial map. -/
def scaledQuotientEndProjMap [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (f : σ → MvPolynomial σ k) (hf : ∀ i, (f i).IsHomogeneous d)
    (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (f i) ≠ 0) :
    Proj (polynomialQuotientGrading I hI) ⟶ Proj (polynomialQuotientGrading I hI) :=
  DegreeScaledHom.projMap (quotientEndDegreeScaledHom I hI d f hf hpres) hd
    (quotientEndDegreeScaledHom_irrelevant_of_no_basepoint I hI d hd f hf hpres hbase)

@[simp] theorem scaledPolynomialProjMap_preimage_basicOpen [Finite σ]
    (d : ℕ) (hd : 0 < d) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0)
    (p : MvPolynomial ι k) :
    scaledPolynomialProjMap d hd F hF hbase ⁻¹ᵁ
        ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) p =
      ProjectiveSpectrum.basicOpen (homogeneousSubmodule σ k) (aeval F p) := rfl

@[simp] theorem scaledQuotientCoordinateProjMap_preimage_basicOpen [Finite σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (F i) ≠ 0)
    (p : MvPolynomial ι k) :
    scaledQuotientCoordinateProjMap I hI d hd F hF hbase ⁻¹ᵁ
        ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) p =
      ProjectiveSpectrum.basicOpen (polynomialQuotientGrading I hI)
        (Ideal.Quotient.mk I (aeval F p)) := rfl

@[simp] theorem scaledQuotientEndProjMap_preimage_basicOpen [Finite σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (d : ℕ) (hd : 0 < d)
    (f : σ → MvPolynomial σ k) (hf : ∀ i, (f i).IsHomogeneous d)
    (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (f i) ≠ 0)
    (p : MvPolynomial σ k ⧸ I) :
    scaledQuotientEndProjMap I hI d hd f hf hpres hbase ⁻¹ᵁ
        ProjectiveSpectrum.basicOpen (polynomialQuotientGrading I hI) p =
      ProjectiveSpectrum.basicOpen (polynomialQuotientGrading I hI)
        (quotientEnd I f hpres p) := rfl

end ArithDyn.Extension
