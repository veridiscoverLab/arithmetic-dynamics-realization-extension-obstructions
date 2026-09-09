import ArithDyn.Extension.ScaledProjMapLawsCore

/-!
# Composition and extensionality of scaled Proj maps

These are equalities of scheme morphisms, proved on the entire structure sheaf.
They allow a commuting square of the original graded quotient rings to descend
to the same square of projective schemes, with all nilpotent information retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry ProjectiveSpectrum Proj StructureSheaf

namespace ArithDyn.Extension.DegreeScaledHom

variable {A B C σ τ ψ : Type u} [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  {d e : ℕ}

/-- Contravariance on the actual projective schemes. -/
theorem projMap_comp (f : DegreeScaledHom 𝒜 ℬ d) (g : DegreeScaledHom ℬ 𝒞 e)
    (hd : 0 < d) (he : 0 < e)
    (hf : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map f.1).radical)
    (hg : 𝒞₊.toIdeal ≤ (ℬ₊.toIdeal.map g.1).radical) :
    projMap (comp g f) (Nat.mul_pos he hd) (irrelevant_le_radical_comp f g hf hg) =
      projMap g he hg ≫ projMap f hd hf := by
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.Hom.ext'
  exact congrArg (fun m => m.hom) (sheafedSpaceMap_comp f g hd he hf hg)

/-- Degree witnesses do not change a morphism induced by the same ring map. -/
theorem projMap_congr (f : DegreeScaledHom 𝒜 ℬ d) (g : DegreeScaledHom 𝒜 ℬ e)
    (hd : 0 < d) (he : 0 < e)
    (hf : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map f.1).radical)
    (hg : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map g.1).radical) (hfg : f.1 = g.1) :
    projMap f hd hf = projMap g he hg := by
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.Hom.ext'
  exact congrArg (fun m => m.hom) (sheafedSpaceMap_congr f g hd he hf hg hfg)

end ArithDyn.Extension.DegreeScaledHom
