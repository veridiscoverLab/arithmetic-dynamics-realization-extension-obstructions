import ArithDyn.Extension.ScaledHomogeneousMap

/-!
# Proj morphisms for degree-multiplying homomorphisms

The construction follows the structure-sheaf and stalk construction of Mathlib's
`ProjectiveSpectrum.Functor` (Kenny Lau, Apache 2.0), now using the actual scaled
homogeneous localizations. It produces scheme morphisms on the original graded
rings, allowing the same projective object to carry its polarized self-map.
-/

set_option autoImplicit false
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
  {d e : ℕ} (f : DegreeScaledHom 𝒜 ℬ d) (hd : 0 < d)
  (hf : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map f.1).radical)

/-- Comap on the homogeneous prime ideals of the original rings. -/
def pointMap (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := idealComap f hd p.1
  isPrime := p.isPrime.comap f.1
  not_irrelevant_le h := p.not_irrelevant_le <| toIdeal_le_toIdeal_iff.mp <|
    hf.trans (p.isPrime.radical_le_iff.mpr (Ideal.map_le_of_le_comap h))

def continuousMap : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := pointMap f hd hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s => ⟨f.1 '' s, by ext; simp [pointMap, idealComap]; rfl⟩

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 ⊆ continuousMap f hd hf ⁻¹' U.1)

def sectionMapFun (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtPrime ℬ y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl (s ⟨continuousMap f hd hf y.1, hUV y.2⟩)

theorem isLocallyFraction_sectionMapFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (sectionMapFun f hd hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨continuousMap f hd hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, hfrac⟩
  refine ⟨W.comap (continuousMap f hd hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, d * i,
    ⟨f.1 a, f.2 i a a.2⟩, ⟨f.1 b, f.2 i b b.2⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ => hb ⟨_, hqW⟩, ?_⟩
  rintro ⟨q, hqW, hqV⟩
  apply val_injective
  specialize hfrac ⟨_, hqW⟩
  simp_all [sectionMapFun, Localization.localRingHom_mk]

def sectionMap :
    (Proj.structureSheaf 𝒜).1.obj (.op U) →+* (Proj.structureSheaf ℬ).1.obj (.op V) where
  toFun s := ⟨sectionMapFun f hd hf U V hUV s.1,
    isLocallyFraction_sectionMapFun f hd hf U V hUV s.1 s.2⟩
  map_one' := by ext; simp [sectionMapFun]
  map_zero' := by ext; simp [sectionMapFun]
  map_add' x y := by ext; simp [sectionMapFun]
  map_mul' x y := by ext; simp [sectionMapFun]

def sheafedSpaceMap : Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom (continuousMap f hd hf)
      c := { app U := CommRingCat.ofHom (sectionMap f hd hf _ _ Set.Subset.rfl) } }

lemma germ_map_sectionInBasicOpen {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (pointMap f hd hf p).1.toIdeal.primeCompl) :
    (toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (sheafedSpaceMap f hd hf).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap f hd hf).hom.c.app _ (sectionInBasicOpen 𝒜 _ c)) =
    (toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen ℬ (f.1 c.den)) p c.den_mem
      (sectionInBasicOpen ℬ p (mapFraction f le_rfl c)) := rfl

theorem localRingHom_comp_stalkIso (p : ProjectiveSpectrum ℬ) :
    (Proj.stalkIso 𝒜 (pointMap f hd hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫ (Proj.stalkIso ℬ p).inv =
      (sheafedSpaceMap f hd hf).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, Proj.stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply, Localization.localRingHom_mk]
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_map_sectionInBasicOpen]
  erw [stalkIso'_germ]
  simp [mapFraction]

/-- The actual scheme morphism associated with a positive-degree homogeneous map. -/
def projMap : Proj ℬ ⟶ Proj 𝒜 where
  __ := (sheafedSpaceMap f hd hf).hom
  prop p := .mk fun x hx => by
    rw [← localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (Proj.stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (Proj.stalkIso 𝒜 (pointMap f hd hf p)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

@[simp] theorem projMap_preimage_basicOpen (s : A) :
    projMap f hd hf ⁻¹ᵁ ProjectiveSpectrum.basicOpen 𝒜 s = ProjectiveSpectrum.basicOpen ℬ (f.1 s) := rfl

end ArithDyn.Extension.DegreeScaledHom
