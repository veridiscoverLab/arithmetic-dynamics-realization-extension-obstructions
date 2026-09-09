import ArithDyn.Extension.Iterates
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Actual quotient-algebra dynamics and the affine `Spec` square

The polynomial congruence from Theorem 3.1 is converted here into an equality of actual
`k`-algebra homomorphisms.  The quotient is by the original ideal `I`, not its radical;
in particular this construction retains nilpotent elements of the coordinate algebra.
The same equality is preserved by every iterate and yields a commuting square of
`Scheme.Hom`s after applying `Spec`.

These are affine-cone statements.  No identification with a `Proj` morphism, no projective
closed immersion, and no ample-line-bundle comparison is asserted in this file.
-/

set_option autoImplicit false

namespace ArithDyn.Extension

open MvPolynomial

variable {k : Type*} [CommRing k] {σ ν : Type*}

/-- The pullback on the original quotient algebra induced by an ideal-preserving
polynomial self-map.  There is no radical operation in this definition. -/
noncomputable def quotientEnd (I : Ideal (MvPolynomial σ k))
    (f : σ → MvPolynomial σ k) (hpres : ∀ g ∈ I, aeval f g ∈ I) :
    (MvPolynomial σ k ⧸ I) →ₐ[k] (MvPolynomial σ k ⧸ I) :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ k I).comp (aeval f))
    (fun g hg => Ideal.Quotient.eq_zero_iff_mem.2 (hpres g hg))

@[simp] theorem quotientEnd_mk (I : Ideal (MvPolynomial σ k))
    (f : σ → MvPolynomial σ k) (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (g : MvPolynomial σ k) :
    quotientEnd I f hpres (Ideal.Quotient.mk I g) =
      Ideal.Quotient.mk I (aeval f g) := rfl

/-- The coordinate-algebra map of `j` on the original quotient. -/
noncomputable def quotientCoordinates (I : Ideal (MvPolynomial σ k))
    (j : ν → MvPolynomial σ k) :
    MvPolynomial ν k →ₐ[k] (MvPolynomial σ k ⧸ I) :=
  (Ideal.Quotient.mkₐ k I).comp (aeval j)

@[simp] theorem quotientCoordinates_apply (I : Ideal (MvPolynomial σ k))
    (j : ν → MvPolynomial σ k) (g : MvPolynomial ν k) :
    quotientCoordinates I j g = Ideal.Quotient.mk I (aeval j g) := rfl

/-- The polynomial congruence is an actual commuting square of `k`-algebra homomorphisms. -/
theorem quotient_commuting_square (I : Ideal (MvPolynomial σ k))
    (j : ν → MvPolynomial σ k) (Ψ : ν → MvPolynomial ν k)
    (f : σ → MvPolynomial σ k) (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hcomm : ∀ a, aeval j (Ψ a) - aeval f (j a) ∈ I) :
    (quotientCoordinates I j).comp (aeval Ψ) =
      (quotientEnd I f hpres).comp (quotientCoordinates I j) := by
  apply MvPolynomial.algHom_ext
  intro a
  simpa only [AlgHom.comp_apply, quotientCoordinates_apply, aeval_X, quotientEnd_mk]
    using (Ideal.Quotient.eq.2 (hcomm a))

/-- Evaluation at the polynomial iterate equals the iterate of the evaluation algebra map. -/
theorem aeval_iterMap_eq_pow (f : σ → MvPolynomial σ k) (n : ℕ) :
    (aeval (iterMap f n) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k) = (aeval f) ^ n := by
  induction n with
  | zero =>
    apply MvPolynomial.algHom_ext
    intro a
    simp [iterMap]
  | succ n ih =>
    rw [pow_succ', ← ih]
    apply MvPolynomial.algHom_ext
    intro a
    simp [iterMap, AlgHom.mul_apply]

/-- Every polynomial iterate still preserves the same original ideal. -/
theorem iterMap_preserves_ideal (I : Ideal (MvPolynomial σ k))
    (f : σ → MvPolynomial σ k) (hpres : ∀ g ∈ I, aeval f g ∈ I) (n : ℕ) :
    ∀ g ∈ I, aeval (iterMap f n) g ∈ I := by
  intro g hg
  rw [aeval_iterMap_eq_pow]
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [pow_succ', AlgHom.mul_apply]
    exact hpres _ ih

/-- The quotient pullback respects all iterates, on every element of the original quotient. -/
theorem quotientEnd_pow_mk (I : Ideal (MvPolynomial σ k))
    (f : σ → MvPolynomial σ k) (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (n : ℕ) (g : MvPolynomial σ k) :
    ((quotientEnd I f hpres) ^ n) (Ideal.Quotient.mk I g) =
      Ideal.Quotient.mk I (aeval (iterMap f n) g) := by
  induction n with
  | zero => simp [iterMap]
  | succ n ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, quotientEnd_mk]
    congr 1
    simp only [aeval_iterMap_eq_pow, pow_succ', AlgHom.mul_apply]

/-- Quotienting the polynomial iterate and iterating the quotient map agree as algebra maps. -/
theorem quotientEnd_iterMap (I : Ideal (MvPolynomial σ k))
    (f : σ → MvPolynomial σ k) (hpres : ∀ g ∈ I, aeval f g ∈ I) (n : ℕ) :
    quotientEnd I (iterMap f n) (iterMap_preserves_ideal I f hpres n) =
      (quotientEnd I f hpres) ^ n := by
  apply AlgHom.ext
  intro x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (quotientEnd_pow_mk I f hpres n g).symm

/-- All iterates commute in the same quotient algebra, with no pointwise reduction. -/
theorem quotient_commuting_square_iterates (I : Ideal (MvPolynomial σ k))
    (j : ν → MvPolynomial σ k) (Ψ : ν → MvPolynomial ν k)
    (f : σ → MvPolynomial σ k) (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hcomm : ∀ a, aeval j (Ψ a) - aeval f (j a) ∈ I) (n : ℕ) :
    (quotientCoordinates I j).comp ((aeval Ψ) ^ n) =
      ((quotientEnd I f hpres) ^ n).comp (quotientCoordinates I j) := by
  rw [← aeval_iterMap_eq_pow, ← quotientEnd_iterMap I f hpres n]
  exact quotient_commuting_square I j (iterMap Ψ n) (iterMap f n)
    (iterMap_preserves_ideal I f hpres n) (iterMap_compat I j Ψ f hpres hcomm n)

section Spectra

open AlgebraicGeometry CategoryTheory

universe u v

/-- Contravariance turns an actual algebra square into a square of scheme morphisms. -/
theorem specMap_of_algHom_square {R : Type v} {A B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (j : A →ₐ[R] B) (F : A →ₐ[R] A) (f : B →ₐ[R] B)
    (h : j.comp F = f.comp j) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom j.toRingHom) =
      Spec.map (CommRingCat.ofHom j.toRingHom) ≫ Spec.map (CommRingCat.ofHom F.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun h : A →ₐ[R] B => Spec.map (CommRingCat.ofHom h.toRingHom)) h.symm

/-- The morphism induced by an algebra homomorphism commutes with the actual structure
morphisms to `Spec R`. -/
theorem specMap_algHom_over_base {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (j : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom j.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => j.commutes r)

/-- Algebra-map powers give actual repeated composition of scheme morphisms. -/
theorem specMap_algHom_pow {R : Type v} {A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (f : A →ₐ[R] A) (n : ℕ) :
    Spec.map (CommRingCat.ofHom (f ^ n).toRingHom) =
      ((End.of (Spec.map (CommRingCat.ofHom f.toRingHom))) ^ n).asHom := by
  induction n with
  | zero =>
    change Spec.map (𝟙 (CommRingCat.of A)) = 𝟙 _
    exact Spec.map_id _
  | succ n ih =>
    calc
      Spec.map (CommRingCat.ofHom (f ^ (n + 1)).toRingHom) =
          Spec.map (CommRingCat.ofHom (f ^ n).toRingHom) ≫
            Spec.map (CommRingCat.ofHom f.toRingHom) := by
        rw [pow_succ]
        exact Spec.map_comp (CommRingCat.ofHom f.toRingHom)
          (CommRingCat.ofHom (f ^ n).toRingHom)
      _ = ((End.of (Spec.map (CommRingCat.ofHom f.toRingHom))) ^ (n + 1)).asHom := by
        rw [ih, pow_succ', End.mul_def]

variable {R : Type u} [CommRing R] {ι τ : Type v}

/-- The actual self-morphism of the affine scheme defined by the original quotient. -/
noncomputable def quotientSpecEnd (I : Ideal (MvPolynomial ι R))
    (f : ι → MvPolynomial ι R) (hpres : ∀ g ∈ I, aeval f g ∈ I) :
    Spec (CommRingCat.of (MvPolynomial ι R ⧸ I)) ⟶
      Spec (CommRingCat.of (MvPolynomial ι R ⧸ I)) :=
  Spec.map (CommRingCat.ofHom (quotientEnd I f hpres).toRingHom)

/-- The actual morphism from the quotient's affine scheme to the ambient affine space. -/
noncomputable def quotientSpecCoordinates (I : Ideal (MvPolynomial ι R))
    (j : τ → MvPolynomial ι R) :
    Spec (CommRingCat.of (MvPolynomial ι R ⧸ I)) ⟶
      Spec (CommRingCat.of (MvPolynomial τ R)) :=
  Spec.map (CommRingCat.ofHom (quotientCoordinates I j).toRingHom)

/-- One step of the extension gives a genuine `Scheme.Hom` square on the affine cones. -/
theorem quotientSpec_commuting_square (I : Ideal (MvPolynomial ι R))
    (j : τ → MvPolynomial ι R) (Ψ : τ → MvPolynomial τ R)
    (f : ι → MvPolynomial ι R) (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hcomm : ∀ a, aeval j (Ψ a) - aeval f (j a) ∈ I) :
    quotientSpecEnd I f hpres ≫ quotientSpecCoordinates I j =
      quotientSpecCoordinates I j ≫ Spec.map (CommRingCat.ofHom (aeval Ψ).toRingHom) :=
  specMap_of_algHom_square (quotientCoordinates I j) (aeval Ψ) (quotientEnd I f hpres)
    (quotient_commuting_square I j Ψ f hpres hcomm)

/-- Every iterate yields the same square of actual scheme morphisms. -/
theorem quotientSpec_commuting_square_iterates (I : Ideal (MvPolynomial ι R))
    (j : τ → MvPolynomial ι R) (Ψ : τ → MvPolynomial τ R)
    (f : ι → MvPolynomial ι R) (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hcomm : ∀ a, aeval j (Ψ a) - aeval f (j a) ∈ I) (n : ℕ) :
    Spec.map (CommRingCat.ofHom ((quotientEnd I f hpres) ^ n).toRingHom) ≫
        quotientSpecCoordinates I j =
      quotientSpecCoordinates I j ≫ Spec.map (CommRingCat.ofHom ((aeval Ψ) ^ n).toRingHom) :=
  specMap_of_algHom_square (quotientCoordinates I j) ((aeval Ψ) ^ n)
    ((quotientEnd I f hpres) ^ n) (quotient_commuting_square_iterates I j Ψ f hpres hcomm n)

/-- The square in terms of genuine iterates in the endomorphism monoid of schemes. -/
theorem quotientSpec_commuting_square_powers (I : Ideal (MvPolynomial ι R))
    (j : τ → MvPolynomial ι R) (Ψ : τ → MvPolynomial τ R)
    (f : ι → MvPolynomial ι R) (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hcomm : ∀ a, aeval j (Ψ a) - aeval f (j a) ∈ I) (n : ℕ) :
    ((End.of (quotientSpecEnd I f hpres)) ^ n).asHom ≫ quotientSpecCoordinates I j =
      quotientSpecCoordinates I j ≫
        ((End.of (Spec.map (CommRingCat.ofHom (aeval Ψ).toRingHom))) ^ n).asHom := by
  simpa only [quotientSpecEnd, specMap_algHom_pow]
    using quotientSpec_commuting_square_iterates I j Ψ f hpres hcomm n

end Spectra

end ArithDyn.Extension
