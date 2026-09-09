/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Scheme-valued functoriality of Proj under a radical irrelevant-ideal condition

This adapts Mathlib's projective-spectrum functor construction.  The hypothesis
`ℬ₊ ≤ 𝒜₊.map f` is weakened to
`ℬ₊.toIdeal ≤ (𝒜₊.map f).toIdeal.radical`.
The output is an actual morphism between Mathlib's Proj schemes, with its local
homomorphisms of structure sheaves and stalks, not just a map of points.
-/


universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj

namespace AlgebraicGeometry

section universe_polymorphic

variable {A B C σ τ ψ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (hf : ℬ₊.toIdeal ≤ (𝒜₊.map f).toIdeal.radical)
  (hg : 𝒞₊.toIdeal ≤ (ℬ₊.map g).toIdeal.radical)

namespace ProjectiveSpectrum

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
@[simps] def comapRadicalFun (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le le := p.3 <| toIdeal_le_toIdeal_iff.mp <|
    hf.trans <| p.2.radical_le_iff.mpr <|
      toIdeal_le_toIdeal_iff.mpr (map_le_of_le_comap _ le)

/-- The underlying continuous function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
def comapRadical : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := comapRadicalFun f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by ext; simp⟩

end ProjectiveSpectrum

namespace Proj

open StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 ⊆ ProjectiveSpectrum.comapRadical f hf ⁻¹' U.1)

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def comapRadicalStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtPrime ℬ y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl <| s ⟨.comapRadical f hf y.1, hUV y.2⟩

set_option backward.isDefEq.respectTransparency false in
lemma isLocallyFraction_comapRadicalStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (comapRadicalStructureSheafFun f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨.comapRadical f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (ProjectiveSpectrum.comapRadical f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [comapRadicalStructureSheafFun]

set_option backward.isDefEq.respectTransparency false in
/-- The underlying ring hom of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def comapRadicalStructureSheaf :
    (Proj.structureSheaf 𝒜).1.obj (.op U) →+* (Proj.structureSheaf ℬ).1.obj (.op V) where
  toFun s := ⟨comapRadicalStructureSheafFun _ _ _ _ hUV s.1,
      isLocallyFraction_comapRadicalStructureSheafFun _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [comapRadicalStructureSheafFun]
  map_zero' := by ext; simp [comapRadicalStructureSheafFun]
  map_add' x y := by ext; simp [comapRadicalStructureSheafFun]
  map_mul' x y := by ext; simp [comapRadicalStructureSheafFun]

end Proj

end universe_polymorphic

section universe_monomorphic

namespace Proj

variable {A B C σ τ ψ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (hf : ℬ₊.toIdeal ≤ (𝒜₊.map f).toIdeal.radical)
  (hg : 𝒞₊.toIdeal ≤ (ℬ₊.map g).toIdeal.radical)

/-- The underlying map of `Proj ℬ ⟶ Proj 𝒜` on the level of sheafed spaces. -/
@[simps! (isSimp := false)] noncomputable def sheafedSpaceMapRadical :
    Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom <| comapRadical f hf
      c := { app U := CommRingCat.ofHom <| comapRadicalStructureSheaf f hf _ _ Set.Subset.rfl } }

lemma germ_mapRadical_sectionInBasicOpen {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (p.comapRadical f hf).1.toIdeal.primeCompl) :
    (toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (sheafedSpaceMapRadical f hf).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMapRadical f hf).hom.c.app _ (sectionInBasicOpen 𝒜 _ c)) =
    (toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen ℬ p (c.map _ le_rfl)) :=
  rfl

@[elementwise] theorem localRingHom_comp_stalkIsoRadical (p : ProjectiveSpectrum ℬ) :
    (stalkIso 𝒜 (ProjectiveSpectrum.comapRadical f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (stalkIso ℬ p).inv =
      (sheafedSpaceMapRadical f hf).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply]
  simp only [GradedRingHom.toRingHom_eq_toRingHom, Localization.localRingHom_mk,
    GradedRingHom.coe_toRingHom]
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_mapRadical_sectionInBasicOpen]
  erw [stalkIso'_germ]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality of `Proj`. -/
noncomputable def mapRadical : Proj ℬ ⟶ Proj 𝒜 where
  __ := (sheafedSpaceMapRadical f hf).hom
  prop p := .mk fun x hx ↦ by
    rw [← localRingHom_comp_stalkIsoRadical] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (stalkIso 𝒜 (p.comapRadical f hf)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

@[simp] theorem mapRadical_preimage_basicOpen (s : A) :
    mapRadical f hf ⁻¹ᵁ basicOpen 𝒜 s = basicOpen ℬ (f s) := rfl

theorem ι_comp_mapRadical (s : A) : (basicOpen ℬ (f s)).ι ≫ mapRadical f hf =
    (mapRadical f hf).resLE _ _ le_rfl ≫ (basicOpen 𝒜 s).ι := by simp

@[reassoc] lemma awayToSection_comp_appLERadical {i : ℕ} {s : A} (hs : s ∈ 𝒜 i) :
    awayToSection 𝒜 s ≫
      Scheme.Hom.appLE (mapRadical f hf) (basicOpen 𝒜 s) (basicOpen ℬ (f s)) (by rfl) =
    CommRingCat.ofHom (Away.map f s : Away 𝒜 s →+* Away ℬ (f s)) ≫
      awayToSection ℬ (f s) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hs
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/--
The following square commutes:
```
Proj ℬ         ⟶ Proj 𝒜₁
    ^                   ^
    |                   |
Spec A₂[f(s)⁻¹]₀ ⟶ Spec A₁[s⁻¹]₀
```
-/
@[reassoc] theorem awayι_comp_mapRadical {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    awayι ℬ (f s) (f.2 hs) hi ≫ mapRadical f hf =
    Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ awayι 𝒜 s hs hi := by
  rw [awayι, awayι, Category.assoc, ι_comp_mapRadical, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (basicOpen ℬ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, awayToSection_comp_appLERadical _ _ hs]


/-- The radical construction agrees with Mathlib's map when its stronger
irrelevant-ideal containment hypothesis is available. -/
theorem mapRadical_eq_map (hstrong : ℬ₊ ≤ 𝒜₊.map f) :
    mapRadical f hf = Proj.map f hstrong := by
  rfl

end Proj

end universe_monomorphic

end AlgebraicGeometry
