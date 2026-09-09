import Mathlib

/-!
# Geometric points over a specialisation (a Chevalley-type extension lemma)

Let `L` be a field, `R ⊆ L` a subring and `ψ : R →+* K₀` a ring homomorphism to a field. Then there
is a valuation subring `B` of `L` containing `R` whose maximal ideal meets `R` exactly in `ker ψ`:
for `r ∈ R` we have `B.valuation r < 1 ↔ ψ r = 0` (`exists_valuationSubring_of_ringHom`).

Proof: `P := ker ψ` is a prime ideal of `R`, the local subring `A := R_P` (`LocalSubring.ofPrime`)
is dominated by some valuation subring `B` (`LocalSubring.exists_le_valuationSubring`); domination
means that an element of `A` is a unit in `B` iff it is a unit in `A`, and for `r ∈ R` the element
`r` is a unit of `R_P` iff `r ∉ P`.

We also record that the residue map `B → κ(B)` kills exactly the elements of valuation `< 1`
(`residue_eq_zero_iff_valuation_lt_one`), and that two ring homomorphisms `R → K₁`, `R → K₂` into
fields with the same kernel `P` factor through a common field `κ = Frac(R ⧸ P)` embedding into both
(`exists_common_field`). Together these identify the "residue point" of `R` in `B` with `ψ` up to
an embedding of residue fields.
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

universe u

/-- The residue map of a valuation subring kills exactly the elements of valuation `< 1`, i.e. its
kernel is the maximal ideal, expressed through the valuation. -/
theorem residue_eq_zero_iff_valuation_lt_one {L : Type*} [Field L] (B : ValuationSubring L)
    (x : B) : IsLocalRing.residue B x = 0 ↔ B.valuation x < 1 :=
  (IsLocalRing.residue_eq_zero_iff x).trans (ValuationSubring.valuation_lt_one_iff B x)

/-- A valuation subring `B ⊇ R` of `L` whose maximal ideal meets `R` exactly in `ker ψ`. -/
theorem exists_valuationSubring_of_ringHom {L K₀ : Type*} [Field L] [Field K₀] (R : Subring L)
    (ψ : R →+* K₀) :
    ∃ B : ValuationSubring L, R ≤ B.toSubring ∧
      ∀ (r : L) (hr : r ∈ R), B.valuation r < 1 ↔ ψ ⟨r, hr⟩ = 0 := by
  haveI hP : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  -- `A = R_P` is dominated by a valuation subring `B`.
  obtain ⟨B, hAB⟩ :=
    LocalSubring.exists_le_valuationSubring (LocalSubring.ofPrime R (RingHom.ker ψ))
  have hRA : R ≤ (LocalSubring.ofPrime R (RingHom.ker ψ)).toSubring :=
    LocalSubring.le_ofPrime R (RingHom.ker ψ)
  have hAB' : (LocalSubring.ofPrime R (RingHom.ker ψ)).toSubring ≤ B.toSubring := hAB.1
  have hloc : IsLocalHom (Subring.inclusion hAB') := hAB.2
  have hRB : R ≤ B.toSubring := hRA.trans hAB'
  refine ⟨B, hRB, fun r hr => ?_⟩
  -- valuation `< 1` means: non-unit of `B`
  have h1 : B.valuation r < 1 ↔ (⟨r, hRB hr⟩ : B) ∈ IsLocalRing.maximalIdeal B :=
    (ValuationSubring.valuation_lt_one_iff B ⟨r, hRB hr⟩).symm
  have h2 : (⟨r, hRB hr⟩ : B) ∈ IsLocalRing.maximalIdeal B ↔ ¬ IsUnit (⟨r, hRB hr⟩ : B) :=
    (IsLocalRing.mem_maximalIdeal _).trans mem_nonunits_iff
  -- domination: unit in `B` iff unit in `A` (the element of `B` is the image of that of `A`)
  have h3 : IsUnit (⟨r, hRB hr⟩ : B) ↔ IsUnit (Subring.inclusion hRA ⟨r, hr⟩) :=
    ⟨fun hu => hloc.map_nonunit (Subring.inclusion hRA ⟨r, hr⟩) hu,
      fun hu => hu.map (Subring.inclusion hAB')⟩
  -- unit in `A = R_P` iff not in `P`
  have h4 : IsUnit (Subring.inclusion hRA ⟨r, hr⟩) ↔ (⟨r, hr⟩ : R) ∈ (RingHom.ker ψ).primeCompl :=
    IsLocalization.AtPrime.isUnit_to_map_iff
      (LocalSubring.ofPrime R (RingHom.ker ψ)).toSubring (RingHom.ker ψ) ⟨r, hr⟩
  rw [h1, h2, h3, h4, Ideal.mem_primeCompl_iff, not_not, RingHom.mem_ker]

/-- Two ring homs from `R` into fields with the same kernel `P` factor through a common field
`κ = Frac(R ⧸ P)` (living in the universe of `R`) which embeds into both fields: there are
`θ : R →+* κ` and injective `ι₁ : κ →+* K₁`, `ι₂ : κ →+* K₂` with `ι₁ ∘ θ = φ₁` and
`ι₂ ∘ θ = φ₂`. -/
theorem exists_common_field {R : Type u} {K₁ K₂ : Type*} [CommRing R] [Field K₁] [Field K₂]
    (φ₁ : R →+* K₁) (φ₂ : R →+* K₂) (h : ∀ r, φ₁ r = 0 ↔ φ₂ r = 0) :
    ∃ (κ : Type u) (_ : Field κ) (θ : R →+* κ) (ι₁ : κ →+* K₁) (ι₂ : κ →+* K₂),
      Function.Injective ι₁ ∧ Function.Injective ι₂ ∧ ι₁.comp θ = φ₁ ∧ ι₂.comp θ = φ₂ := by
  haveI hP : (RingHom.ker φ₁).IsPrime := RingHom.ker_isPrime φ₁
  -- both maps kill `P = ker φ₁`, hence descend injectively to the domain `R ⧸ P`
  have H₁ : ∀ a : R, a ∈ RingHom.ker φ₁ → φ₁ a = 0 := fun a ha => RingHom.mem_ker.mp ha
  have H₂ : ∀ a : R, a ∈ RingHom.ker φ₁ → φ₂ a = 0 :=
    fun a ha => (h a).mp (RingHom.mem_ker.mp ha)
  have hg₁ : Function.Injective (Ideal.Quotient.lift (RingHom.ker φ₁) φ₁ H₁) :=
    RingHom.lift_injective_of_ker_le_ideal (RingHom.ker φ₁) H₁ le_rfl
  have hg₂ : Function.Injective (Ideal.Quotient.lift (RingHom.ker φ₁) φ₂ H₂) :=
    RingHom.lift_injective_of_ker_le_ideal (RingHom.ker φ₁) H₂
      (fun a ha => RingHom.mem_ker.mpr ((h a).mpr (RingHom.mem_ker.mp ha)))
  -- extend to the fraction field of `R ⧸ P`
  refine ⟨FractionRing (R ⧸ RingHom.ker φ₁), inferInstance,
    (algebraMap (R ⧸ RingHom.ker φ₁) (FractionRing (R ⧸ RingHom.ker φ₁))).comp
      (Ideal.Quotient.mk (RingHom.ker φ₁)),
    IsFractionRing.lift hg₁, IsFractionRing.lift hg₂, ?_, ?_, ?_, ?_⟩
  · exact RingHom.injective _
  · exact RingHom.injective _
  · ext r
    simp [IsFractionRing.lift_algebraMap, Ideal.Quotient.lift_mk]
  · ext r
    simp [IsFractionRing.lift_algebraMap, Ideal.Quotient.lift_mk]

end ArithDyn.Derksen
