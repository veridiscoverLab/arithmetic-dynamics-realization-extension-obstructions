import ArithDyn.Extension.ProjRadical
import ArithDyn.Extension.HomogeneousCoordinates

/-!
# Scheme morphisms from homogeneous coordinate systems of positive degree

A degree `d` coordinate substitution preserves degrees when its domain polynomial
ring is graded by assigning weight `d` to every variable.  The radical certificate
deduced from geometric base-point freeness then constructs an actual morphism of
Proj schemes.  The codomain is explicitly the constantly weighted Proj; identifying
it with standard Proj is a separate regrading step.
-/

set_option autoImplicit false

universe u v

namespace ArithDyn.Extension

open MvPolynomial HomogeneousIdeal AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable {k : Type u} {σ ι : Type v} [Field k]

/-- The polynomial grading assigning degree `d` to each variable. -/
abbrev constantWeightGrading (ι : Type v) (k : Type u) [Field k] (d : ℕ) :=
  weightedHomogeneousSubmodule k (fun _ : ι => d)

/-- Substitution of degree `d` forms takes constant-weight degree `m` to standard
degree `m`.  No nonzero-polynomial or divisibility premise is needed. -/
theorem weighted_aeval_isHomogeneous (d m : ℕ) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d) {p : MvPolynomial ι k}
    (hp : p.IsWeightedHomogeneous (fun _ : ι => d) m) :
    (aeval F p).IsHomogeneous m := by
  apply IsHomogeneous.sum
  intro a ha
  apply IsHomogeneous.C_mul
  convert IsHomogeneous.prod _ _ (fun i => d * a i) (fun i _ => (hF i).pow (a i)) using 1
  rw [← hp (mem_support_iff.mp ha), Finsupp.weight_apply]
  simp only [Finsupp.sum, smul_eq_mul, mul_comm]

/-- The graded ring homomorphism underlying the degree `d` coordinate system. -/
noncomputable def degreeSubstitution (d : ℕ) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d) :
    constantWeightGrading ι k d →+*ᵍ homogeneousSubmodule σ k where
  __ := (aeval F).toRingHom
  map_mem {m} {p} hp := weighted_aeval_isHomogeneous d m F hF (p := p) hp

@[simp] theorem degreeSubstitution_apply (d : ℕ) (F : ι → MvPolynomial σ k)
    (hF : ∀ i, (F i).IsHomogeneous d) (p : MvPolynomial ι k) :
    degreeSubstitution d F hF p = aeval F p := rfl

/-- Each output coordinate belongs to the image of the weighted irrelevant ideal. -/
theorem coordinateIdeal_le_map_weighted_irrelevant (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d) :
    Ideal.span (Set.range F) ≤
      ((irrelevant (constantWeightGrading ι k d)).map (degreeSubstitution d F hF)).toIdeal := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have hi : X i ∈ (irrelevant (constantWeightGrading ι k d)).toIdeal :=
    mem_irrelevant_of_mem _ hd (isWeightedHomogeneous_X k (fun _ : ι => d) i)
  simpa using Ideal.mem_map_of_mem (degreeSubstitution d F hF) hi

/-- The coordinate-ideal radical certificate supplies exactly the hypothesis
required by the scheme-valued `Proj.mapRadical`. -/
theorem irrelevant_le_radical_map_degreeSubstitution (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (Ideal.span (Set.range F)).radical) :
    (irrelevant (homogeneousSubmodule σ k)).toIdeal ≤
      (((irrelevant (constantWeightGrading ι k d)).map
        (degreeSubstitution d F hF)).toIdeal).radical := by
  rw [standard_irrelevant_eq_coordinateIdeal]
  exact hbase.trans (Ideal.radical_mono
    (coordinateIdeal_le_map_weighted_irrelevant d hd F hF))

/-- A genuine scheme morphism associated to a positive-degree coordinate system,
with its constantly weighted codomain recorded in its type. -/
noncomputable def degreeMapOfRadical (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (Ideal.span (Set.range F)).radical) :
    Proj (homogeneousSubmodule σ k) ⟶ Proj (constantWeightGrading ι k d) :=
  Proj.mapRadical (degreeSubstitution d F hF)
    (irrelevant_le_radical_map_degreeSubstitution d hd F hF hbase)

/-- Geometric base-point freeness over the algebraic closure gives a morphism
over the original field, including its structure sheaf and local stalk maps. -/
noncomputable def degreeMap [Finite σ] (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0) :
    Proj (homogeneousSubmodule σ k) ⟶ Proj (constantWeightGrading ι k d) :=
  degreeMapOfRadical d hd F hF (coordinateIdeal_le_radical_of_global_no_basepoint F hbase)

@[simp] theorem degreeMapOfRadical_preimage_basicOpen (d : ℕ) (hd : 0 < d)
    (F : ι → MvPolynomial σ k) (hF : ∀ i, (F i).IsHomogeneous d)
    (hbase : Ideal.span (Set.range (X : σ → MvPolynomial σ k)) ≤
      (Ideal.span (Set.range F)).radical) (p : MvPolynomial ι k) :
    degreeMapOfRadical d hd F hF hbase ⁻¹ᵁ
        ProjectiveSpectrum.basicOpen (constantWeightGrading ι k d) p =
      ProjectiveSpectrum.basicOpen (homogeneousSubmodule σ k) (aeval F p) := rfl

end ArithDyn.Extension
