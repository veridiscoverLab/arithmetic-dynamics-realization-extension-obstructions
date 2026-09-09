import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Surjective graded ring maps induce closed immersions on Proj

This file proves the scheme-theoretic output bridge for a degree-preserving
surjection of graded rings.  The proof extracts homogeneous preimages, proves
surjectivity on the degree-zero homogeneous localizations, and applies locality
of closed immersions on the target.  No field or degree-zero-ring hypothesis,
reducedness assumption, or finite-generation assumption is used.

This theorem does not construct a section ring from a scheme or prove that a
chosen ample power gives a surjective graded coordinate map.
-/

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded

universe u

namespace ArithDyn.Extension

set_option backward.isDefEq.respectTransparency false

variable {A B σ τ : Type u}
  [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A surjective degree-preserving map is surjective on each homogeneous piece. -/
theorem exists_homogeneous_preimage (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) {n : ℕ} {b : B} (hb : b ∈ ℬ n) :
    ∃ a : A, a ∈ 𝒜 n ∧ f a = b := by
  obtain ⟨a, ha⟩ := hf b
  refine ⟨DirectSum.decompose 𝒜 a n, (DirectSum.decompose 𝒜 a n).property, ?_⟩
  rw [f.map_directSumDecompose, ha]
  exact DirectSum.decompose_of_mem_same ℬ hb

/-- Surjectivity supplies the irrelevant-ideal condition required by `Proj.map`. -/
theorem irrelevant_le_map_of_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) : ℬ₊ ≤ 𝒜₊.map f := by
  apply (HomogeneousIdeal.irrelevant_le ℬ).mpr
  intro n hn b hb
  obtain ⟨a, ha, rfl⟩ := exists_homogeneous_preimage f hf hb
  exact Ideal.mem_map_of_mem f (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ha)

/-- The induced map on degree-zero localizations is surjective. -/
theorem away_map_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) {n : ℕ} {s : A} (hs : s ∈ 𝒜 n) :
    Function.Surjective (Away.map f s : Away 𝒜 s →+* Away ℬ (f s)) := by
  intro x
  obtain ⟨m, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.2 hs) x
  obtain ⟨a, ha, hab⟩ := exists_homogeneous_preimage f hf hb
  refine ⟨Away.mk 𝒜 hs m a ha, ?_⟩
  simp only [Away.map_mk, hab]

open AlgebraicGeometry ProjectiveSpectrum Proj

/-- On every homogeneous basic open, a surjective graded map is a closed immersion. -/
theorem proj_map_restrict_isClosedImmersion (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (hrel : ℬ₊ ≤ 𝒜₊.map f)
    {n : ℕ} (hn : 0 < n) {s : A} (hs : s ∈ 𝒜 n) :
    IsClosedImmersion (Proj.map f hrel ∣_ Proj.basicOpen 𝒜 s) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map f s))) :=
    IsClosedImmersion.spec_of_surjective _ (away_map_surjective f hf hs)
  have heq :
      (basicOpenIsoSpec ℬ (f s) (f.2 hs) hn).inv ≫
        (Proj.map f hrel ∣_ Proj.basicOpen 𝒜 s) =
      Spec.map (CommRingCat.ofHom (Away.map f s)) ≫
        (basicOpenIsoSpec 𝒜 s hs hn).inv := by
    apply (cancel_mono (Proj.basicOpen 𝒜 s).ι).mp
    simpa only [Proj.awayι, Category.assoc, morphismRestrict_ι] using
      Proj.awayι_comp_map f hrel hn s hs
  apply (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (basicOpenIsoSpec ℬ (f s) (f.2 hs) hn).inv
    (Proj.map f hrel ∣_ Proj.basicOpen 𝒜 s)).mp
  rw [heq]
  infer_instance

/-- A surjective degree-preserving graded ring homomorphism induces an actual
closed immersion of schemes.  The irrelevant-ideal condition is derived, rather
than assumed as geometric output data. -/
theorem proj_map_isClosedImmersion (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (hrel : ℬ₊ ≤ 𝒜₊.map f) :
    IsClosedImmersion (Proj.map f hrel) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsClosedImmersion)
    (fun i : Σ n : PNat, 𝒜 n ↦ Proj.basicOpen 𝒜 i.2)
  · apply Proj.iSup_basicOpen_eq_top
    apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
    intro n hn a ha
    exact Ideal.subset_span ⟨⟨⟨n, hn⟩, ⟨a, ha⟩⟩, rfl⟩
  · intro i
    exact proj_map_restrict_isClosedImmersion f hf hrel i.1.2 i.2.2

/-- The closed immersion associated to a surjective graded map, with its
irrelevant-ideal condition supplied by the theorem above. -/
theorem proj_map_isClosedImmersion_of_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) :
    IsClosedImmersion (Proj.map f (irrelevant_le_map_of_surjective f hf)) :=
  proj_map_isClosedImmersion f hf _

end ArithDyn.Extension
