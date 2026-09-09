import ArithDyn.Extension.Theorem31
import ArithDyn.Extension.ScaledVeroneseClosedImmersion
import ArithDyn.Extension.QuotientCoordinatePolarization

/-!
# The concrete extension theorem as a projective scheme theorem

The original coordinate theorem now returns a proved closed immersion and an
endomorphism of the same standard projective space, with a commuting square on
actual schemes and all its iterates.  The quotient retains the original ideal.

The inputs are still a homogeneous coordinate presentation and polynomial lifts
of the given self-map.  This theorem does not assert that an arbitrary ample
line bundle has already supplied that presentation or the restriction-surjectivity
hypothesis needed to produce those lifts.
-/

set_option autoImplicit false

noncomputable section

universe u

open MvPolynomial AlgebraicGeometry CategoryTheory

namespace ArithDyn.Extension

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable {k : Type u} [Field k] {r : ℕ}

/-- The concrete coordinate theorem, including its exact projective embedding,
original projective quotient self-map, actual twist pullbacks, ambient extension,
and every iterate. -/
theorem theorem_3_1_projective
    (I : Ideal (MvPolynomial (Fin (r + 1)) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (r + 1)) k))
    (hX : (projZeros (AlgebraicClosure k) I).Nonempty)
    (d : ℕ) (hd : 2 ≤ d)
    (f : Fin (r + 1) → MvPolynomial (Fin (r + 1)) k)
    (hf : ∀ i, (f i).IsHomogeneous d)
    (hbase : ∀ v ∈ projZeros (AlgebraicClosure k) I, ∃ i, aeval v (f i) ≠ 0)
    (hpres : ∀ g ∈ I, aeval f g ∈ I) :
    let hd0 : 0 < d := by omega
    let hfbase := fun v hv hvan => hbase v ⟨hv, hvan⟩
    let φ := scaledQuotientEndProjMap I hI d hd0 f hf hpres hfbase
    ∃ (ν : Type) (_ : Fintype ν) (s : ℕ) (hs : 0 < s)
      (j : ν → MvPolynomial (Fin (r + 1)) k) (Ψ : ν → MvPolynomial ν k)
      (hj : ∀ i, (j i).IsHomogeneous s) (hΨ : ∀ i, (Ψ i).IsHomogeneous d)
      (hjbase : ∀ v : Fin (r + 1) → AlgebraicClosure k, v ≠ 0 →
        (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (j i) ≠ 0)
      (hΨbase : ∀ v : ν → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (Ψ i) ≠ 0),
      let jX := scaledQuotientCoordinateProjMap I hI s hs j hj hjbase
      let ΨX := scaledPolynomialProjMap d hd0 Ψ hΨ hΨbase
      (∀ (n : ℕ) (g : MvPolynomial (Fin (r + 1)) k), g.IsHomogeneous (n * s) →
        ∃ G : MvPolynomial ν k, G.IsHomogeneous n ∧ aeval j G = g) ∧
      IsClosedImmersion jX ∧
      Nonempty ((Scheme.Modules.pullback jX).obj (ProjTwist.standardO k ν 1) ≅
        quotientCoordinateTwist I hI s) ∧
      Nonempty ((Scheme.Modules.pullback ΨX).obj (ProjTwist.standardO k ν 1) ≅
        ProjTwist.standardO k ν d) ∧
      φ ≫ jX = jX ≫ ΨX ∧
      ∀ n : ℕ, ((End.of φ) ^ n).asHom ≫ jX = jX ≫ ((End.of ΨX) ^ n).asHom := by
  dsimp only
  obtain ⟨ν, hν, s, j, Ψ, hs, hj, hjbase, hgen, hΨ, hΨbase, hcomm⟩ :=
    theorem_3_1 I hI hX d hd f hf hbase hpres
  letI := hν
  have hs0 : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hd0 : 0 < d := by omega
  have hjbase0 : ∀ v : Fin (r + 1) → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (j i) ≠ 0 :=
    fun v hv hvan => hjbase v ⟨hv, hvan⟩
  have hfbase0 : ∀ v : Fin (r + 1) → AlgebraicClosure k, v ≠ 0 →
      (∀ g ∈ I, aeval v g = 0) → ∃ i, aeval v (f i) ≠ 0 :=
    fun v hv hvan => hbase v ⟨hv, hvan⟩
  have hsquare := scaledProj_commuting_square I hI s d hs0 hd0 j hj Ψ hΨ f hf
    hpres hjbase0 hΨbase hfbase0 hcomm
  refine ⟨ν, hν, s, hs0, j, Ψ, hj, hΨ, hjbase0, hΨbase, hgen, ?_, ?_, ?_, hsquare, ?_⟩
  · exact scaledQuotientCoordinateProjMap_isClosedImmersion_of_exact_veronese
      I hI s hs0 j hj hjbase0 hgen
  · exact ⟨quotientCoordinatePolarizationIso I hI s hs0 j hj
      (exact_veronese_no_basepoint s j hgen)⟩
  · exact ⟨ProjTwist.scaledPolynomialPolarizationIso d hd0 Ψ hΨ hΨbase⟩
  · exact scheme_commuting_square_powers _ _ _ hsquare

end ArithDyn.Extension
