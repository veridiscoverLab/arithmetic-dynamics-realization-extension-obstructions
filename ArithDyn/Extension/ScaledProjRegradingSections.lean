import ArithDyn.Extension.ScaledProjRegradingCore

/-!
# Compatibility with the original standard projective coordinate maps

The direct scaled construction and the weighted construction followed by the
proved regrading isomorphism induce the same maps on all local fractions.
This comparison keeps the actual standard Proj targets chosen earlier.
-/

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry ProjectiveSpectrum Proj StructureSheaf MvPolynomial

namespace ArithDyn.Extension

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable {k : Type u} [Field k] {ι : Type v} {B τ : Type (max u v)} [CommRing B]
  [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ℕ → τ} [GradedRing ℬ]

/-- Compatibility before packaging sections into sheafed-space morphisms. -/
theorem scaledOfWeighted_sectionMap (d : ℕ) (hd : 0 < d)
    (g : constantWeightGrading ι k d →+*ᵍ ℬ)
    (hg : ℬ₊.toIdeal ≤ ((irrelevant (constantWeightGrading ι k d)).map g).toIdeal.radical)
    (U : Opens (ProjectiveSpectrum (homogeneousSubmodule ι k)))
    (V : Opens (ProjectiveSpectrum ℬ))
    (hUV : V.1 ⊆ DegreeScaledHom.continuousMap (scaledOfWeighted d g) hd
      (scaledOfWeighted_irrelevant d hd g hg) ⁻¹' U.1) :
    DegreeScaledHom.sectionMap (scaledOfWeighted d g) hd
      (scaledOfWeighted_irrelevant d hd g hg) U V hUV =
    (Proj.comapRadicalStructureSheaf g hg
      (U.comap ⟨(constantWeightHomeomorph d hd).symm,
        (constantWeightHomeomorph d hd).continuous_invFun⟩) V hUV).comp
      (sectionToConstantWeight d hd U
        (U.comap ⟨(constantWeightHomeomorph d hd).symm,
          (constantWeightHomeomorph d hd).continuous_invFun⟩) Set.Subset.rfl) := by
  apply RingHom.ext
  intro s
  apply Subtype.ext
  funext p
  exact scaledOfWeighted_localRingHom d g
    (DegreeScaledHom.pointMap (scaledOfWeighted d g) hd
      (scaledOfWeighted_irrelevant d hd g hg) p.1).1.toIdeal p.1.1.toIdeal rfl
    (s.1 ⟨DegreeScaledHom.pointMap (scaledOfWeighted d g) hd
      (scaledOfWeighted_irrelevant d hd g hg) p.1, hUV p.2⟩)

end ArithDyn.Extension
