import ArithDyn.Extension.ScaledProjMap
import ArithDyn.Extension.ProjRegrading

/-!
# Compatibility with the original standard projective coordinate maps

The direct scaled construction and the weighted construction followed by the
proved regrading isomorphism induce the same maps on all local fractions.
This comparison keeps the actual standard Proj targets chosen earlier.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry ProjectiveSpectrum Proj StructureSheaf MvPolynomial

namespace ArithDyn.Extension

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable {k : Type u} [Field k] {ι : Type v} {B τ : Type (max u v)} [CommRing B]
  [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ℕ → τ} [GradedRing ℬ]

def scaledOfWeighted (d : ℕ) (g : constantWeightGrading ι k d →+*ᵍ ℬ) :
    DegreeScaledHom (homogeneousSubmodule ι k) ℬ d :=
  ⟨g.toRingHom, fun _ _ hx => g.2 (isWeightedHomogeneous_of_isHomogeneous d hx)⟩

theorem scaledOfWeighted_irrelevant (d : ℕ) (hd : 0 < d)
    (g : constantWeightGrading ι k d →+*ᵍ ℬ)
    (hg : ℬ₊.toIdeal ≤ ((irrelevant (constantWeightGrading ι k d)).map g).toIdeal.radical) :
    ℬ₊.toIdeal ≤ ((irrelevant (homogeneousSubmodule ι k)).toIdeal.map
      (scaledOfWeighted d g).1).radical := by
  change ℬ₊.toIdeal ≤ ((irrelevant (homogeneousSubmodule ι k)).toIdeal.map g.toRingHom).radical
  rw [← constantWeight_irrelevant_eq d hd]
  exact hg

theorem scaledOfWeighted_localRingHom (d : ℕ)
    (g : constantWeightGrading ι k d →+*ᵍ ℬ)
    (I : Ideal (MvPolynomial ι k)) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (hIJ : I = J.comap g.toRingHom)
    (x : AtPrime (homogeneousSubmodule ι k) I) :
    DegreeScaledHom.localRingHom (scaledOfWeighted d g) I J hIJ x =
      HomogeneousLocalization.localRingHom g I J hIJ
        (localizationToConstantWeight (k := k) (ι := ι) d I.primeCompl x) := by
  apply val_injective
  simp only [DegreeScaledHom.val_localRingHom, HomogeneousLocalization.val_localRingHom,
    val_localizationToConstantWeight]
  rfl

end ArithDyn.Extension
