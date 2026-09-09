import ArithDyn.Extension.ProjMapLaws

/-!
# Compatibility of radical Proj maps with the degree-zero base

The naturality square is proved as an equality of actual scheme morphisms.
It does not identify the degree-zero ring of an arbitrary section algebra with a field.
-/

set_option autoImplicit false

universe u

open HomogeneousIdeal HomogeneousLocalization CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The homogeneous localization maps commute with the maps from degree zero. -/
theorem away_map_comp_fromZeroRingHom (f : 𝒜 →+*ᵍ ℬ) (s : A) :
    (Away.map f s).comp (fromZeroRingHom 𝒜 (Submonoid.powers s)) =
      (fromZeroRingHom ℬ (Submonoid.powers (f s))).comp f.gradedZeroRingHom := by
  ext x
  simp [fromZeroRingHom, Away.map, HomogeneousLocalization.map_mk]

set_option backward.isDefEq.respectTransparency false in
/-- The actual Proj map is compatible with its degree-zero base map. -/
theorem mapRadical_toSpecZero (f : 𝒜 →+*ᵍ ℬ)
    (hf : ℬ₊.toIdeal ≤ (𝒜₊.map f).toIdeal.radical) :
    mapRadical f hf ≫ toSpecZero 𝒜 = toSpecZero ℬ ≫
      Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  refine (mapRadicalAffineOpenCover f hf).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f,
    mapRadicalAffineOpenCover_f, ← Category.assoc,
    awayι_comp_mapRadical f hf s.1.2 _ s.2.2]
  rw [Category.assoc, awayι_toSpecZero, awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (away_map_comp_fromZeroRingHom f s.2)

end AlgebraicGeometry.Proj
