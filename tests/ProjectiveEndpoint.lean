import ArithDyn.Extension.Theorem31Projective
import ArithDyn.Extension.ProjCoordinateBasis

set_option autoImplicit false
noncomputable section
universe u
open MvPolynomial AlgebraicGeometry CategoryTheory ArithDyn.Extension
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

/-- Arbitrary field universe; the original and final finite coordinate indices stay in Type 0. -/
example (k : Type u) [Field k] (r : ℕ)
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
    ∃ (ν : Type) (_ : Fintype ν)
      (j : Proj (polynomialQuotientGrading I hI) ⟶ Proj (homogeneousSubmodule ν k)),
      IsClosedImmersion j ∧
      ∃ (Ψ : Proj (homogeneousSubmodule ν k) ⟶ Proj (homogeneousSubmodule ν k)),
        ∀ n : ℕ, ((End.of φ) ^ n).asHom ≫ j = j ≫ ((End.of Ψ) ^ n).asHom := by
  dsimp only
  obtain ⟨ν, hν, s, hs, j, Ψ, hj, hΨ, hjbase, hΨbase, _, hclosed, _, _, _, hpow⟩ :=
    theorem_3_1_projective I hI hX d hd f hf hbase hpres
  exact ⟨ν, hν, _, hclosed, _, hpow⟩

#print axioms ArithDyn.Extension.theorem_3_1_projective
#print axioms ArithDyn.Extension.quotientCoordinatePolarizationIso
#print axioms ArithDyn.Extension.ProjTwist.homogeneousBasisPullbackIso
