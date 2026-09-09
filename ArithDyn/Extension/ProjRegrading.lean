import ArithDyn.Extension.ProjRegradingCore

/-!
# Constant positive regrading of Proj

Reindexing all polynomial degrees by multiplication with a positive integer leaves
homogeneous elements and degree-zero localizations unchanged.  The maps below retain
the same underlying polynomials and ambient fractions.  Regrading a scheme does not
identify its degree-one twists: the weighted degree `d` twist corresponds to standard
degree one; no assertion about twists is made here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

namespace ArithDyn.Extension

open MvPolynomial HomogeneousIdeal AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable {k : Type u} {ι : Type v} [Field k]

open HomogeneousLocalization TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf

/-- The regrading morphism of sheafed spaces. -/
def sheafedSpaceToConstantWeight (d : ℕ) (hd : 0 < d) :
    Proj.toSheafedSpace (homogeneousSubmodule ι k) ⟶
      Proj.toSheafedSpace (constantWeightGrading ι k d) where
  hom :=
    { base := TopCat.ofHom ⟨constantWeightHomeomorph d hd, (constantWeightHomeomorph d hd).continuous_toFun⟩
      c := { app U := CommRingCat.ofHom (sectionFromConstantWeight d hd _ _ Set.Subset.rfl) } }

/-- The inverse regrading morphism of sheafed spaces. -/
def sheafedSpaceFromConstantWeight (d : ℕ) (hd : 0 < d) :
    Proj.toSheafedSpace (constantWeightGrading ι k d) ⟶
      Proj.toSheafedSpace (homogeneousSubmodule ι k) where
  hom :=
    { base := TopCat.ofHom ⟨(constantWeightHomeomorph d hd).symm, (constantWeightHomeomorph d hd).continuous_invFun⟩
      c := { app U := CommRingCat.ofHom (sectionToConstantWeight d hd _ _ Set.Subset.rfl) } }

/-- The regrading section maps are inverse on standard Proj. -/
theorem sheafedSpaceToConstantWeight_comp_from (d : ℕ) (hd : 0 < d) :
    sheafedSpaceToConstantWeight (k := k) (ι := ι) d hd ≫
      sheafedSpaceFromConstantWeight d hd =
        𝟙 (Proj.toSheafedSpace (homogeneousSubmodule ι k)) := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.ext _ _ rfl ?_
  ext U s
  apply Subtype.ext
  funext p
  change localizationFromConstantWeight (k := k) (ι := ι) d hd p.1.1.toIdeal.primeCompl
    (localizationToConstantWeight (k := k) (ι := ι) d p.1.1.toIdeal.primeCompl (s.1 p)) = s.1 p
  exact (localizationConstantWeightEquiv d hd p.1.1.toIdeal.primeCompl).left_inv (s.1 p)

/-- The regrading section maps are inverse on weighted Proj. -/
theorem sheafedSpaceFromConstantWeight_comp_to (d : ℕ) (hd : 0 < d) :
    sheafedSpaceFromConstantWeight (k := k) (ι := ι) d hd ≫
      sheafedSpaceToConstantWeight d hd =
        𝟙 (Proj.toSheafedSpace (constantWeightGrading ι k d)) := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.ext _ _ rfl ?_
  ext U s
  apply Subtype.ext
  funext p
  change localizationToConstantWeight (k := k) (ι := ι) d p.1.1.toIdeal.primeCompl
    (localizationFromConstantWeight (k := k) (ι := ι) d hd p.1.1.toIdeal.primeCompl (s.1 p)) = s.1 p
  exact (localizationConstantWeightEquiv d hd p.1.1.toIdeal.primeCompl).right_inv (s.1 p)

/-- The regrading isomorphism includes the full structure sheaf. -/
def constantWeightSheafedSpaceIso (d : ℕ) (hd : 0 < d) :
    Proj.toSheafedSpace (homogeneousSubmodule ι k) ≅
      Proj.toSheafedSpace (constantWeightGrading ι k d) where
  hom := sheafedSpaceToConstantWeight d hd
  inv := sheafedSpaceFromConstantWeight d hd
  hom_inv_id := sheafedSpaceToConstantWeight_comp_from d hd
  inv_hom_id := sheafedSpaceFromConstantWeight_comp_to d hd

/-- A scheme isomorphism between standard Proj and constant positive weighted Proj.
It makes no assertion identifying the degree-one twists for the two gradings. -/
def constantWeightProjIso (d : ℕ) (hd : 0 < d) :
    Proj (homogeneousSubmodule ι k) ≅ Proj (constantWeightGrading ι k d) :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (LocallyRingedSpace.isoOfSheafedSpaceIso (constantWeightSheafedSpaceIso d hd))

@[simp] theorem constantWeightProjIso_hom_preimage_basicOpen
    (d : ℕ) (hd : 0 < d) (p : MvPolynomial ι k) :
    (constantWeightProjIso d hd).hom ⁻¹ᵁ
        ProjectiveSpectrum.basicOpen (constantWeightGrading ι k d) p =
      ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) p := rfl

@[simp] theorem constantWeightProjIso_inv_preimage_basicOpen
    (d : ℕ) (hd : 0 < d) (p : MvPolynomial ι k) :
    (constantWeightProjIso d hd).inv ⁻¹ᵁ
        ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) p =
      ProjectiveSpectrum.basicOpen (constantWeightGrading ι k d) p := rfl

/-- A degree `d` coordinate system now gives a morphism between standard Proj
schemes on both ends, by composing with the proved regrading isomorphism. -/
def standardDegreeMapOfRadical {σ : Type v} (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (Ideal.span (Set.range F)).radical) :
    Proj (homogeneousSubmodule σ k) ⟶ Proj (homogeneousSubmodule ι k) :=
  degreeMapOfRadical d hd F hF hbase ≫ (constantWeightProjIso d hd).inv

/-- Geometric base-point freeness produces a genuine morphism between standard
projective schemes over the original field.  Pullback of the twisting sheaf is a
separate statement, not hidden in this type. -/
def standardDegreeMap {σ : Type v} [Finite σ] (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0) :
    Proj (homogeneousSubmodule σ k) ⟶ Proj (homogeneousSubmodule ι k) :=
  standardDegreeMapOfRadical d hd F hF
    (coordinateIdeal_le_radical_of_global_no_basepoint F hbase)

@[simp] theorem standardDegreeMapOfRadical_preimage_basicOpen {σ : Type v}
    (d : ℕ) (hd : 0 < d) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (Ideal.span (Set.range F)).radical) (p : MvPolynomial ι k) :
    standardDegreeMapOfRadical d hd F hF hbase ⁻¹ᵁ
        ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) p =
      ProjectiveSpectrum.basicOpen (homogeneousSubmodule σ k) (aeval F p) := rfl

@[simp] theorem standardDegreeMap_preimage_basicOpen {σ : Type v} [Finite σ]
    (d : ℕ) (hd : 0 < d) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0)
    (p : MvPolynomial ι k) :
    standardDegreeMap d hd F hF hbase ⁻¹ᵁ
        ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) p =
      ProjectiveSpectrum.basicOpen (homogeneousSubmodule σ k) (aeval F p) := rfl

end ArithDyn.Extension
