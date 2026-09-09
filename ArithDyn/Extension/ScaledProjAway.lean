import ArithDyn.Extension.ScaledProjMap
import ArithDyn.Extension.ProjClosedImmersion

/-!
# Affine charts of the actual degree-scaled Proj morphism

All chart maps are maps of the degree-zero localizations of the original rings.
The chart square is an equality of scheme morphisms, proved through their
structure-sheaf maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry ProjectiveSpectrum Proj StructureSheaf

namespace ArithDyn.Extension.DegreeScaledHom

variable {A B S T : Type u} [CommRing A] [CommRing B]
  [SetLike S A] [AddSubgroupClass S A] [SetLike T B] [AddSubgroupClass T B]
  {𝒜 : ℕ → S} {ℬ : ℕ → T} [GradedRing 𝒜] [GradedRing ℬ]
  {d : ℕ} (f : DegreeScaledHom 𝒜 ℬ d)

def awayMap (a : A) : Away 𝒜 a →+* Away ℬ (f.1 a) :=
  localizationMap f (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩)

@[simp] theorem awayMap_mk {i : ℕ} {a : A} (ha : a ∈ 𝒜 i)
    (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • i)) :
    awayMap f a (Away.mk 𝒜 ha n x hx) =
      Away.mk ℬ (f.2 i a ha) n (f.1 x)
        (by simpa only [smul_eq_mul, Nat.mul_left_comm] using f.2 (n • i) x hx) := by
  apply val_injective
  simp [awayMap, Away.mk, mapFraction, Localization.mk_eq_mk']

variable (hd : 0 < d) (hf : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map f.1).radical)

@[reassoc] theorem awayToSection_comp_appLE {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) :
    AlgebraicGeometry.Proj.awayToSection 𝒜 a ≫
      (projMap f hd hf).appLE (Proj.basicOpen 𝒜 a) (Proj.basicOpen ℬ (f.1 a)) le_rfl =
    CommRingCat.ofHom (awayMap f a) ≫ AlgebraicGeometry.Proj.awayToSection ℬ (f.1 a) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 ha x
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, awayMap_mk]
  refine Subtype.ext <| funext fun p => ?_
  change HomogeneousLocalization.mk _ = HomogeneousLocalization.mk _
  apply val_injective
  simp [mapFraction]

theorem basicOpen_ι_comp_projMap (a : A) :
    (Proj.basicOpen ℬ (f.1 a)).ι ≫ projMap f hd hf =
      (projMap f hd hf).resLE _ _ le_rfl ≫ (Proj.basicOpen 𝒜 a).ι := by
  simp
  rfl

@[reassoc] theorem awayι_comp_projMap {i : ℕ} (hi : 0 < i) (a : A) (ha : a ∈ 𝒜 i) :
    awayι ℬ (f.1 a) (f.2 i a ha) (Nat.mul_pos hd hi) ≫ projMap f hd hf =
      Spec.map (CommRingCat.ofHom (awayMap f a)) ≫ awayι 𝒜 a ha hi := by
  rw [awayι, awayι, Category.assoc, basicOpen_ι_comp_projMap,
    ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (Proj.basicOpen ℬ (f.1 a)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, awayToSection_comp_appLE f hd hf ha]

/-- The original morphism is a closed immersion on any chart whose actual
zero-degree localization map is surjective. -/
theorem projMap_restrict_isClosedImmersion_of_away_surjective
    {i : ℕ} (hi : 0 < i) {a : A} (ha : a ∈ 𝒜 i)
    (hsurj : Function.Surjective (awayMap f a)) :
    IsClosedImmersion (projMap f hd hf ∣_ Proj.basicOpen 𝒜 a) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (awayMap f a))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  have heq :
      (basicOpenIsoSpec ℬ (f.1 a) (f.2 i a ha) (Nat.mul_pos hd hi)).inv ≫
        (projMap f hd hf ∣_ Proj.basicOpen 𝒜 a) =
      Spec.map (CommRingCat.ofHom (awayMap f a)) ≫
        (basicOpenIsoSpec 𝒜 a ha hi).inv := by
    apply (cancel_mono (Proj.basicOpen 𝒜 a).ι).mp
    simpa only [Proj.awayι, Category.assoc, morphismRestrict_ι] using
      awayι_comp_projMap f hd hf hi a ha
  apply (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (basicOpenIsoSpec ℬ (f.1 a) (f.2 i a ha) (Nat.mul_pos hd hi)).inv
    (projMap f hd hf ∣_ Proj.basicOpen 𝒜 a)).mp
  rw [heq]
  infer_instance

end ArithDyn.Extension.DegreeScaledHom
