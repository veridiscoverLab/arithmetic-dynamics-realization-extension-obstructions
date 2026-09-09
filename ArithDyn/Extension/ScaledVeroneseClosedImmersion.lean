import ArithDyn.Extension.ScaledProjAway
import ArithDyn.Extension.ScaledCoordinateMaps
import ArithDyn.Extension.VeroneseProjClosedImmersion

/-!
# Closed immersion of the original degree-scaled Veronese coordinates

The input certificate covers every Veronese layer modulo the original homogeneous
ideal. It makes each actual chart map surjective, without asserting surjectivity
of the whole substitution homomorphism or replacing the ideal by its radical.
Both endpoints carry their original standard gradings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u v

namespace ArithDyn.Extension

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj MvPolynomial GradedQuotient

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable {k : Type u} {σ ι : Type v} [Field k]

/-- Every numerator in the original quotient chart is lifted in its own
homogeneous Veronese layer. -/
theorem scaled_veronese_awayMap_surjective (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (s : ℕ)
    (j : ι → MvPolynomial σ k) (hj : ∀ i, (j i).IsHomogeneous s)
    (hgen : GeneratesVeroneseModulo I s j) (i : ι) :
    Function.Surjective
      (DegreeScaledHom.awayMap (quotientCoordinatesDegreeScaledHom I hI s j hj) (X i)) := by
  let f := quotientCoordinatesDegreeScaledHom I hI s j hj
  have hi : X i ∈ homogeneousSubmodule ι k 1 := isHomogeneous_X k i
  have hfi : f.1 (X i) ∈ polynomialQuotientGrading I hI s := by
    simpa only [Nat.mul_one] using f.2 1 (X i) hi
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective _ hfi z
  obtain ⟨g, hg, hgb⟩ := Submodule.mem_map.mp hb
  obtain ⟨G, hG, hGj⟩ := hgen n g (by simpa only [smul_eq_mul] using hg)
  have hGb : f.1 G = b := by
    change Ideal.Quotient.mk I (aeval j G) = b
    exact (Ideal.Quotient.eq.mpr hGj).trans hgb
  refine ⟨Away.mk (homogeneousSubmodule ι k) hi n G (by simpa using hG), ?_⟩
  change DegreeScaledHom.awayMap f (X i) _ = _
  rw [DegreeScaledHom.awayMap_mk]
  apply val_injective
  simp only [Away.mk, val_mk, hGb]

/-- The original native standard-Proj coordinate map is a closed immersion.
No comparison with a regraded alternative map is used. -/
theorem scaledQuotientCoordinateProjMap_isClosedImmersion_of_veronese [Finite σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (s : ℕ) (hs : 0 < s)
    (j : ι → MvPolynomial σ k) (hj : ∀ i, (j i).IsHomogeneous s)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (j i) ≠ 0)
    (hgen : GeneratesVeroneseModulo I s j) :
    IsClosedImmersion (scaledQuotientCoordinateProjMap I hI s hs j hj hbase) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun i : ι => Proj.basicOpen (homogeneousSubmodule ι k) (X i))
  · apply Proj.iSup_basicOpen_eq_top
    rw [standard_irrelevant_eq_coordinateIdeal]
  · intro i
    exact DegreeScaledHom.projMap_restrict_isClosedImmersion_of_away_surjective
      (quotientCoordinatesDegreeScaledHom I hI s j hj) hs
      (quotientCoordinatesDegreeScaledHom_irrelevant_of_no_basepoint I hI s hs j hj hbase)
      (by omega : 0 < (1 : ℕ)) (isHomogeneous_X k i)
      (scaled_veronese_awayMap_surjective I hI s j hj hgen i)

/-- The exact all-layer certificate returned for the original `j` is sufficient. -/
theorem scaledQuotientCoordinateProjMap_isClosedImmersion_of_exact_veronese [Finite σ]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (s : ℕ) (hs : 0 < s)
    (j : ι → MvPolynomial σ k) (hj : ∀ i, (j i).IsHomogeneous s)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (j i) ≠ 0)
    (hgen : ∀ (n : ℕ) (g : MvPolynomial σ k), g.IsHomogeneous (n * s) →
      ∃ G : MvPolynomial ι k, G.IsHomogeneous n ∧ aeval j G = g) :
    IsClosedImmersion (scaledQuotientCoordinateProjMap I hI s hs j hj hbase) :=
  scaledQuotientCoordinateProjMap_isClosedImmersion_of_veronese I hI s hs j hj hbase
    (generatesVeroneseModulo_of_exact I s j hgen)

end ArithDyn.Extension
