import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Internal grading of an external algebra of sections

An actual family of section modules with graded multiplication first gives an
external direct sum algebra.  This file constructs its internal homogeneous
submodules and proves the finite homogeneous decomposition, so that the result
can be used by the project's `GradedAlgebra`, section lifting and `Proj` APIs.
-/

universe u v

open DirectSum

namespace ArithDyn.Extension.SectionAlgebra

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {R : Type v} [CommRing R] (F : ℕ → Type u)
  [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
  [DirectSum.GCommRing F] [DirectSum.GAlgebra R F]

/-- The true homogeneous submodule in the external section algebra. -/
def directSumComponent (n : ℕ) : Submodule R (⨁ n, F n) :=
  (DirectSum.lof R ℕ F n).range

omit [DirectSum.GCommRing F] [DirectSum.GAlgebra R F] in
theorem lof_mem_directSumComponent (n : ℕ) (x : F n) :
    DirectSum.lof R ℕ F n x ∈ directSumComponent (R := R) F n := ⟨x, rfl⟩

instance directSumComponent_gradedMonoid :
    SetLike.GradedMonoid (directSumComponent (R := R) F) where
  one_mem := ⟨GradedMonoid.GOne.one, rfl⟩
  mul_mem := by
    intro n m x y hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    refine ⟨GradedMonoid.GMul.mul a b, ?_⟩
    simp [DirectSum.lof_eq_of, DirectSum.of_mul_of]

/-- The original degree module identifies with its embedded homogeneous submodule. -/
def directSumComponentMap (n : ℕ) : F n →ₗ[R] directSumComponent (R := R) F n :=
  (DirectSum.lof R ℕ F n).rangeRestrict

omit [DirectSum.GCommRing F] [DirectSum.GAlgebra R F] in
@[simp] theorem directSumComponentMap_coe (n : ℕ) (x : F n) :
    (directSumComponentMap (R := R) F n x : ⨁ n, F n) = DirectSum.lof R ℕ F n x := rfl

/-- The actual finite homogeneous decomposition into the embedded submodules. -/
def directSumDecompose : (⨁ n, F n) →ₗ[R] ⨁ n, directSumComponent (R := R) F n :=
  DirectSum.lmap (directSumComponentMap (R := R) F)

omit [DirectSum.GCommRing F] [DirectSum.GAlgebra R F] in
theorem directSumDecompose_left_inv :
    DirectSum.coeLinearMap (directSumComponent (R := R) F) ∘ₗ directSumDecompose (R := R) F =
      LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  simp [directSumDecompose]

omit [DirectSum.GCommRing F] [DirectSum.GAlgebra R F] in
theorem directSumDecompose_right_inv :
    directSumDecompose (R := R) F ∘ₗ DirectSum.coeLinearMap (directSumComponent (R := R) F) =
      LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  obtain ⟨a, hax⟩ := x.property
  have hx : x = directSumComponentMap (R := R) F n a := Subtype.ext hax.symm
  subst x
  simp [directSumDecompose]

/-- This constructs the internal grading; no decomposition assumption is supplied. -/
instance directSumGradedAlgebra : GradedAlgebra (directSumComponent (R := R) F) where
  __ := directSumComponent_gradedMonoid (R := R) F
  __ := DirectSum.Decomposition.ofLinearMap (directSumComponent (R := R) F)
    (directSumDecompose (R := R) F) (directSumDecompose_left_inv (R := R) F)
    (directSumDecompose_right_inv (R := R) F)

/-- Each external degree element is recovered unchanged in its true degree. -/
theorem directSum_decompose_lof (n : ℕ) (x : F n) :
    (DirectSum.decompose (directSumComponent (R := R) F)
      (DirectSum.lof R ℕ F n x) n : ⨁ n, F n) = DirectSum.lof R ℕ F n x :=
  DirectSum.decompose_of_mem_same _ (lof_mem_directSumComponent (R := R) F n x)

end

end ArithDyn.Extension.SectionAlgebra
