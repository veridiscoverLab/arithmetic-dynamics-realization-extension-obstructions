import ArithDyn.Extension.ProjRadical

/-!
# Affine covers and composition for the radical Proj construction

The basic opens pulled back from the target cover the source under radical irrelevant
containment.  This yields the composition law for actual scheme morphisms, including
their structure sheaves.  No stronger ideal containment is assumed.
-/

set_option autoImplicit false

universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum

namespace AlgebraicGeometry.Proj

variable {A B C σ τ ψ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- Positive homogeneous elements whose ideal contains the irrelevant ideal up to
radical still give an affine open cover of the original Proj scheme. -/
noncomputable def affineOpenCoverOfIrrelevantLERadical {ι : Type u}
    (a : ι → A) {m : ι → ℕ} (ha : ∀ i, a i ∈ 𝒜 (m i)) (hm : ∀ i, 0 < m i)
    (hcover : 𝒜₊.toIdeal ≤ (Ideal.span (Set.range a)).radical) :
    (Proj 𝒜).AffineOpenCover := by
  have hpoint : ∀ x : ProjectiveSpectrum 𝒜, ∃ i, a i ∉ x.asHomogeneousIdeal := by
    intro x
    by_contra! h
    apply x.not_irrelevant_le
    exact toIdeal_le_toIdeal_iff.mp (hcover.trans (x.isPrime.radical_le_iff.mpr
      (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i))))
  exact {
    I₀ := ι
    X i := .of (Away 𝒜 (a i))
    f i := awayι 𝒜 (a i) (ha i) (hm i)
    idx x := (hpoint x).choose
    covers x := by
      change x ∈ (awayι 𝒜 _ _ _).opensRange
      rw [opensRange_awayι]
      exact (hpoint x).choose_spec }

/-- Radical irrelevant containment is preserved by composition of graded maps. -/
theorem irrelevant_le_radical_map_comp (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)
    (hf : ℬ₊.toIdeal ≤ (𝒜₊.map f).toIdeal.radical)
    (hg : 𝒞₊.toIdeal ≤ (ℬ₊.map g).toIdeal.radical) :
    𝒞₊.toIdeal ≤ (𝒜₊.map (g.comp f)).toIdeal.radical := by
  rw [HomogeneousIdeal.map_comp]
  apply hg.trans
  change (ℬ₊.toIdeal.map g).radical ≤ ((𝒜₊.map f).toIdeal.map g).radical
  exact (Ideal.radical_mono (Ideal.map_mono hf)).trans
    ((Ideal.radical_mono (Ideal.map_radical_le g)).trans_eq (Ideal.radical_idem _))

/-- The affine source cover induced by all positive homogeneous target elements. -/
@[simps! I₀ f] noncomputable def mapRadicalAffineOpenCover (f : 𝒜 →+*ᵍ ℬ)
    (hf : ℬ₊.toIdeal ≤ (𝒜₊.map f).toIdeal.radical) : (Proj ℬ).AffineOpenCover :=
  affineOpenCoverOfIrrelevantLERadical (fun s : (affineOpenCover 𝒜).I₀ => f s.2)
    (fun s => f.2 s.2.2) (fun s => s.1.2) <|
    hf.trans (Ideal.radical_mono (Ideal.map_le_of_le_comap
      ((toIdeal_irrelevant_le _).mpr (fun i hi x hx =>
        Ideal.subset_span ⟨⟨⟨i, hi⟩, ⟨x, hx⟩⟩, rfl⟩))))

set_option backward.isDefEq.respectTransparency false in
/-- Composition of radical Proj maps as actual scheme morphisms. -/
theorem mapRadical_comp (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)
    (hf : ℬ₊.toIdeal ≤ (𝒜₊.map f).toIdeal.radical)
    (hg : 𝒞₊.toIdeal ≤ (ℬ₊.map g).toIdeal.radical) :
    mapRadical (g.comp f) (irrelevant_le_radical_map_comp f g hf hg) =
      mapRadical g hg ≫ mapRadical f hf := by
  refine (mapRadicalAffineOpenCover _ <|
    irrelevant_le_radical_map_comp f g hf hg).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f,
    mapRadicalAffineOpenCover_f, awayι_comp_mapRadical (g.comp f) _ s.1.2 _ s.2.2]
  simp [awayι_comp_mapRadical_assoc _ _ _ _ (map_mem f s.2.2),
    awayι_comp_mapRadical _ _ _ _ s.2.2]

/-- The radical Proj construction sends the identity to the identity morphism. -/
theorem mapRadical_id : mapRadical (GradedRingHom.id 𝒜)
    (by simpa using (Ideal.le_radical : 𝒜₊.toIdeal ≤ 𝒜₊.toIdeal.radical)) =
      𝟙 (Proj 𝒜) := by
  rw [mapRadical_eq_map _ _ (by simp), Proj.map_id]

end AlgebraicGeometry.Proj
