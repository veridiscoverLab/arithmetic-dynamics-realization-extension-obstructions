import ArithDyn.Extension.QuotientDegreeMap
import ArithDyn.Extension.ProjClosedImmersion

/-!
# The actual closed immersion from a Veronese generation certificate

The certificate used here covers every degree `n * s` of the original polynomial
quotient.  On the target chart `D₊(Yᵢ)`, a source fraction has numerator of degree
`n * s` and denominator `jᵢ ^ n`.  Lifting that numerator proves surjectivity of
the chart ring map.  Consequently the given coordinate morphism, with the original
possibly nonreduced quotient as its domain, is a closed immersion.

The whole polynomial ring is not required to be the image of coordinate
substitution.  All ideal equations remain modulo the original ideal `I`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

namespace ArithDyn.Extension

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj

section LocalClosedImmersion

variable {A B S T : Type w} [CommRing A] [CommRing B]
  [SetLike S A] [AddSubgroupClass S A] [SetLike T B] [AddSubgroupClass T B]
  {𝒜 : ℕ → S} {ℬ : ℕ → T} [GradedRing 𝒜] [GradedRing ℬ]

/-- Surjectivity on one homogeneous localization makes the corresponding
restriction of the radical Proj morphism a closed immersion. -/
theorem proj_mapRadical_restrict_isClosedImmersion_of_away_surjective
    (f : 𝒜 →+*ᵍ ℬ) (hrel : ℬ₊.toIdeal ≤ (𝒜₊.map f).toIdeal.radical)
    {n : ℕ} (hn : 0 < n) {a : A} (ha : a ∈ 𝒜 n)
    (hsurj : Function.Surjective (Away.map f a : Away 𝒜 a →+* Away ℬ (f a))) :
    IsClosedImmersion (Proj.mapRadical f hrel ∣_ Proj.basicOpen 𝒜 a) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map f a))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  have heq :
      (basicOpenIsoSpec ℬ (f a) (f.2 ha) hn).inv ≫
        (Proj.mapRadical f hrel ∣_ Proj.basicOpen 𝒜 a) =
      Spec.map (CommRingCat.ofHom (Away.map f a)) ≫
        (basicOpenIsoSpec 𝒜 a ha hn).inv := by
    apply (cancel_mono (Proj.basicOpen 𝒜 a).ι).mp
    simpa only [Proj.awayι, Category.assoc, morphismRestrict_ι] using
      Proj.awayι_comp_mapRadical f hrel hn a ha
  apply (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (basicOpenIsoSpec ℬ (f a) (f.2 ha) hn).inv
    (Proj.mapRadical f hrel ∣_ Proj.basicOpen 𝒜 a)).mp
  rw [heq]
  infer_instance

end LocalClosedImmersion

open MvPolynomial GradedQuotient

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable {k : Type u} {σ ι : Type v} [Field k]

/-- The all-degree certificate needed for a Veronese coordinate system.  It
retains the original ideal: the lifted numerator agrees modulo `I`, not merely
at geometric points. -/
def GeneratesVeroneseModulo (I : Ideal (MvPolynomial σ k)) (s : ℕ)
    (j : ι → MvPolynomial σ k) : Prop :=
  ∀ (n : ℕ) (g : MvPolynomial σ k), g.IsHomogeneous (n * s) →
    ∃ G : MvPolynomial ι k, G.IsHomogeneous n ∧ aeval j G - g ∈ I

/-- An exact all-degree generation certificate is stronger than the certificate
modulo any given ideal.  This is the certificate returned by `theorem_3_1`. -/
theorem generatesVeroneseModulo_of_exact (I : Ideal (MvPolynomial σ k)) (s : ℕ)
    (j : ι → MvPolynomial σ k)
    (hgen : ∀ (n : ℕ) (g : MvPolynomial σ k), g.IsHomogeneous (n * s) →
      ∃ G : MvPolynomial ι k, G.IsHomogeneous n ∧ aeval j G = g) :
    GeneratesVeroneseModulo I s j := by
  intro n g hg
  obtain ⟨G, hG, hGj⟩ := hgen n g hg
  refine ⟨G, hG, ?_⟩
  rw [hGj, sub_self]
  exact I.zero_mem

/-- The all-degree certificate gives surjectivity of every coordinate chart
ring map.  Its source is the degree-zero localization of the weighted polynomial
ring; its target is the degree-zero localization of the original ideal quotient. -/
theorem veronese_away_map_surjective (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (s : ℕ)
    (j : ι → MvPolynomial σ k) (hj : ∀ i, (j i).IsHomogeneous s)
    (hgen : GeneratesVeroneseModulo I s j) (i : ι) :
    Function.Surjective
      (Away.map (quotientDegreeSubstitution I hI s j hj) (X i) :
        Away (constantWeightGrading ι k s) (X i) →+*
          Away (polynomialQuotientGrading I hI)
            (quotientDegreeSubstitution I hI s j hj (X i))) := by
  let f := quotientDegreeSubstitution I hI s j hj
  have hi : X i ∈ constantWeightGrading ι k s s :=
    isWeightedHomogeneous_X k (fun _ : ι => s) i
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective _ (f.2 hi) z
  obtain ⟨g, hg, hgb⟩ := Submodule.mem_map.mp hb
  obtain ⟨G, hG, hGj⟩ := hgen n g (by simpa only [smul_eq_mul] using hg)
  have hGw : G ∈ constantWeightGrading ι k s (n • s) := by
    simpa only [smul_eq_mul, Nat.mul_comm] using
      isWeightedHomogeneous_of_isHomogeneous s hG
  have hGb : f G = b := by
    change Ideal.Quotient.mk I (aeval j G) = b
    have heq : Ideal.Quotient.mk I (aeval j G) = Ideal.Quotient.mk I g :=
      Ideal.Quotient.eq.mpr hGj
    exact heq.trans hgb
  refine ⟨Away.mk (constantWeightGrading ι k s) hi n G hGw, ?_⟩
  change quotientDegreeSubstitution I hI s j hj G = b at hGb
  simp only [Away.map_mk, hGb]

/-- The actual weighted-target coordinate morphism is a closed immersion when
the given coordinates generate all the Veronese layers modulo the original ideal. -/
theorem quotientDegreeMapOfRadical_isClosedImmersion_of_veronese
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (s : ℕ) (hs : 0 < s)
    (j : ι → MvPolynomial σ k) (hj : ∀ i, (j i).IsHomogeneous s)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (I ⊔ Ideal.span (Set.range j)).radical)
    (hgen : GeneratesVeroneseModulo I s j) :
    IsClosedImmersion (quotientDegreeMapOfRadical I hI s hs j hj hbase) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun i : ι => Proj.basicOpen (constantWeightGrading ι k s) (X i))
  · apply Proj.iSup_basicOpen_eq_top
    rw [constantWeight_irrelevant_eq s hs, standard_irrelevant_eq_coordinateIdeal]
  · intro i
    exact proj_mapRadical_restrict_isClosedImmersion_of_away_surjective
      (quotientDegreeSubstitution I hI s j hj)
      (quotient_irrelevant_le_radical_map I hI s hs j hj hbase) hs
      (isWeightedHomogeneous_X k (fun _ : ι => s) i)
      (veronese_away_map_surjective I hI s j hj hgen i)

/-- The same actual coordinate morphism is a closed immersion after identifying
the constant-weight target with standard Proj. -/
theorem quotientStandardDegreeMapOfRadical_isClosedImmersion_of_veronese
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (s : ℕ) (hs : 0 < s)
    (j : ι → MvPolynomial σ k) (hj : ∀ i, (j i).IsHomogeneous s)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (I ⊔ Ideal.span (Set.range j)).radical)
    (hgen : GeneratesVeroneseModulo I s j) :
    IsClosedImmersion (quotientStandardDegreeMapOfRadical I hI s hs j hj hbase) := by
  haveI := quotientDegreeMapOfRadical_isClosedImmersion_of_veronese I hI s hs j hj hbase hgen
  change IsClosedImmersion
    (quotientDegreeMapOfRadical I hI s hs j hj hbase ≫ (constantWeightProjIso s hs).inv)
  infer_instance

/-- With the geometric base-point-free hypothesis used by the original coordinate
construction, all Veronese layers modulo `I` make that very morphism a closed immersion. -/
theorem quotientStandardDegreeMap_isClosedImmersion_of_veronese [Finite σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (s : ℕ) (hs : 0 < s)
    (j : ι → MvPolynomial σ k) (hj : ∀ i, (j i).IsHomogeneous s)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (j i) ≠ 0)
    (hgen : GeneratesVeroneseModulo I s j) :
    IsClosedImmersion (quotientStandardDegreeMap I hI s hs j hj hbase) :=
  quotientStandardDegreeMapOfRadical_isClosedImmersion_of_veronese I hI s hs j hj
    (coordinateIdeal_le_radical_of_no_basepoint I j hbase) hgen

/-- The exact certificate returned for `j` by `theorem_3_1` proves that its
constructed standard-target scheme morphism is a closed immersion. -/
theorem quotientStandardDegreeMap_isClosedImmersion_of_exact_veronese [Finite σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (s : ℕ) (hs : 0 < s)
    (j : ι → MvPolynomial σ k) (hj : ∀ i, (j i).IsHomogeneous s)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (j i) ≠ 0)
    (hgen : ∀ (n : ℕ) (g : MvPolynomial σ k), g.IsHomogeneous (n * s) →
      ∃ G : MvPolynomial ι k, G.IsHomogeneous n ∧ aeval j G = g) :
    IsClosedImmersion (quotientStandardDegreeMap I hI s hs j hj hbase) :=
  quotientStandardDegreeMap_isClosedImmersion_of_veronese I hI s hs j hj hbase
    (generatesVeroneseModulo_of_exact I s j hgen)

end ArithDyn.Extension
