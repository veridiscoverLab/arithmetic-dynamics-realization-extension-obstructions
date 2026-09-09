import ArithDyn.Extension.ScaledProjMap

/-!
# Composition and extensionality of scaled Proj maps

These are equalities of sheafed-space morphisms, proved on the entire structure sheaf.
They allow a commuting square of the original graded quotient rings to descend
to the same square of projective schemes, with all nilpotent information retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
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

theorem irrelevant_le_radical_comp (f : DegreeScaledHom 𝒜 ℬ d)
    (g : DegreeScaledHom ℬ 𝒞 e)
    (hf : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map f.1).radical)
    (hg : 𝒞₊.toIdeal ≤ (ℬ₊.toIdeal.map g.1).radical) :
    𝒞₊.toIdeal ≤ (𝒜₊.toIdeal.map (comp g f).1).radical := by
  change 𝒞₊.toIdeal ≤ (𝒜₊.toIdeal.map (g.1.comp f.1)).radical
  rw [← Ideal.map_map]
  exact hg.trans ((Ideal.radical_mono (Ideal.map_mono hf)).trans
    ((Ideal.radical_mono (Ideal.map_radical_le g.1)).trans_eq (Ideal.radical_idem _)))

/-- Contravariance on the underlying sheafed spaces. -/
theorem sheafedSpaceMap_comp (f : DegreeScaledHom 𝒜 ℬ d) (g : DegreeScaledHom ℬ 𝒞 e)
    (hd : 0 < d) (he : 0 < e)
    (hf : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map f.1).radical)
    (hg : 𝒞₊.toIdeal ≤ (ℬ₊.toIdeal.map g.1).radical) :
    sheafedSpaceMap (comp g f) (Nat.mul_pos he hd) (irrelevant_le_radical_comp f g hf hg) =
      sheafedSpaceMap g he hg ≫ sheafedSpaceMap f hd hf := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.ext _ _ rfl ?_
  ext U s
  apply Subtype.ext
  funext p
  change localRingHom (𝒜 := 𝒜) (ℬ := 𝒞) (comp g f)
      (pointMap (comp g f) (Nat.mul_pos he hd)
        (irrelevant_le_radical_comp f g hf hg) p.1).1.toIdeal p.1.1.toIdeal rfl
      (s.1 ⟨pointMap (comp g f) (Nat.mul_pos he hd)
        (irrelevant_le_radical_comp f g hf hg) p.1, p.2⟩) =
    localRingHom (𝒜 := ℬ) (ℬ := 𝒞) g
      (pointMap g he hg p.1).1.toIdeal p.1.1.toIdeal rfl
      (localRingHom (𝒜 := 𝒜) (ℬ := ℬ) f
        (pointMap f hd hf (pointMap g he hg p.1)).1.toIdeal
        (pointMap g he hg p.1).1.toIdeal rfl
        (s.1 ⟨pointMap (comp g f) (Nat.mul_pos he hd)
          (irrelevant_le_radical_comp f g hf hg) p.1, p.2⟩))
  obtain ⟨c, hc⟩ := (s.1 ⟨pointMap (comp g f) (Nat.mul_pos he hd)
    (irrelevant_le_radical_comp f g hf hg) p.1, p.2⟩).mk_surjective
  rw [← hc]
  apply val_injective
  rfl

/-- Degree witnesses do not change a morphism induced by the same ring map. -/
theorem sheafedSpaceMap_congr (f : DegreeScaledHom 𝒜 ℬ d) (g : DegreeScaledHom 𝒜 ℬ e)
    (hd : 0 < d) (he : 0 < e)
    (hf : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map f.1).radical)
    (hg : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map g.1).radical) (hfg : f.1 = g.1) :
    sheafedSpaceMap f hd hf = sheafedSpaceMap g he hg := by
  rcases f with ⟨f, hfd⟩
  rcases g with ⟨g, hgd⟩
  change f = g at hfg
  subst g
  apply InducedCategory.hom_ext
  refine PresheafedSpace.ext _ _ rfl ?_
  ext U s
  apply Subtype.ext
  funext p
  apply val_injective
  change (localRingHom (𝒜 := 𝒜) (ℬ := ℬ) ⟨f, hfd⟩
      (pointMap ⟨f, hfd⟩ hd hf p.1).1.toIdeal p.1.1.toIdeal rfl
      (s.1 ⟨pointMap ⟨f, hfd⟩ hd hf p.1, p.2⟩)).val =
    (localRingHom (𝒜 := 𝒜) (ℬ := ℬ) ⟨f, hgd⟩
      (pointMap ⟨f, hgd⟩ he hg p.1).1.toIdeal p.1.1.toIdeal rfl
      (s.1 ⟨pointMap ⟨f, hgd⟩ he hg p.1, p.2⟩)).val
  simp only [val_localRingHom]
  rfl

end ArithDyn.Extension.DegreeScaledHom
