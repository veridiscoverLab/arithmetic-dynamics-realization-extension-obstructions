import ArithDyn.Extension.ProjClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual graded quotients by homogeneous ideals

The pieces of the quotient are the images of the original pieces.  Homogeneity
is used to descend the original direct-sum decomposition, and the two inverse
identities are proved.  Thus the quotient grading is constructed here, not
supplied as an additional input.  The ideal is not replaced by its radical.
-/

open DirectSum HomogeneousIdeal CategoryTheory AlgebraicGeometry Graded

universe u v

namespace ArithDyn.Extension.GradedQuotient

set_option backward.isDefEq.respectTransparency false

variable {R : Type v} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
variable (I : HomogeneousIdeal 𝒜)

/-- The actual degree-`n` image submodule in the original ideal quotient. -/
def component (n : ℕ) : Submodule R (A ⧸ I.toIdeal) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

theorem mk_mem_component {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I.toIdeal a ∈ component 𝒜 I n :=
  Submodule.mem_map.mpr ⟨a, ha, rfl⟩

instance component_gradedMonoid : SetLike.GradedMonoid (component 𝒜 I) where
  one_mem := by
    exact mk_mem_component 𝒜 I (SetLike.GradedOne.one_mem (A := 𝒜))
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    exact ⟨a * b, SetLike.mul_mem_graded ha hb,
      map_mul (Ideal.Quotient.mkₐ R I.toIdeal) a b⟩

/-- The quotient map on a single homogeneous component. -/
def componentMap (n : ℕ) : 𝒜 n →ₗ[R] component 𝒜 I n :=
  ((Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap.comp (𝒜 n).subtype).codRestrict _
    (fun a ↦ mk_mem_component 𝒜 I a.property)

@[simp] theorem componentMap_coe (n : ℕ) (a : 𝒜 n) :
    (componentMap 𝒜 I n a : A ⧸ I.toIdeal) = Ideal.Quotient.mk I.toIdeal a := rfl

/-- The original homogeneous decomposition, with each component mapped to the quotient. -/
noncomputable def decomposeBeforeQuotient : A →ₗ[R] ⨁ n, component 𝒜 I n :=
  (DirectSum.lmap (componentMap 𝒜 I)).comp (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

/-- Homogeneity is precisely what makes the mapped decomposition vanish on the ideal. -/
theorem ideal_le_ker_decompose :
    I.toIdeal.restrictScalars R ≤ (decomposeBeforeQuotient 𝒜 I).ker := by
  intro a ha
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  change Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 a n) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.is_homogeneous' n ha)

/-- The decomposition on the quotient, defined by linear quotient descent. -/
noncomputable def decomposeQuotient : (A ⧸ I.toIdeal) →ₗ[R] ⨁ n, component 𝒜 I n :=
  (I.toIdeal.restrictScalars R).liftQ (decomposeBeforeQuotient 𝒜 I)
    (ideal_le_ker_decompose 𝒜 I)

@[simp] theorem decomposeQuotient_mk (a : A) :
    decomposeQuotient 𝒜 I (Ideal.Quotient.mk I.toIdeal a) =
      decomposeBeforeQuotient 𝒜 I a := rfl

theorem coe_lmap_componentMap :
    DirectSum.coeLinearMap (component 𝒜 I) ∘ₗ DirectSum.lmap (componentMap 𝒜 I) =
      (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap ∘ₗ DirectSum.coeLinearMap 𝒜 := by
  apply DirectSum.linearMap_ext
  intro n
  ext a
  simp

theorem decomposeQuotient_left_inv :
    DirectSum.coeLinearMap (component 𝒜 I) ∘ₗ decomposeQuotient 𝒜 I =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change DirectSum.coeLinearMap (component 𝒜 I)
    (DirectSum.lmap (componentMap 𝒜 I) (DirectSum.decompose 𝒜 a)) = _
  change (DirectSum.coeLinearMap (component 𝒜 I) ∘ₗ
    DirectSum.lmap (componentMap 𝒜 I)) (DirectSum.decompose 𝒜 a) = _
  rw [coe_lmap_componentMap]
  change Ideal.Quotient.mk I.toIdeal ((DirectSum.decompose 𝒜).symm
    (DirectSum.decompose 𝒜 a)) = Ideal.Quotient.mk I.toIdeal a
  rw [Equiv.symm_apply_apply]

theorem decomposeQuotient_right_inv :
    decomposeQuotient 𝒜 I ∘ₗ DirectSum.coeLinearMap (component 𝒜 I) =
      LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha, hax⟩ := Submodule.mem_map.mp x.property
  have hx : x = componentMap 𝒜 I n ⟨a, ha⟩ := Subtype.ext hax.symm
  subst x
  simp [decomposeBeforeQuotient, DirectSum.decompose_of_mem 𝒜 ha,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.lof_eq_of]

/-- The grading on the quotient is an actual constructed instance. -/
noncomputable instance quotientGradedAlgebra : GradedAlgebra (component 𝒜 I) where
  __ := component_gradedMonoid 𝒜 I
  __ := DirectSum.Decomposition.ofLinearMap (component 𝒜 I) (decomposeQuotient 𝒜 I)
    (decomposeQuotient_left_inv 𝒜 I) (decomposeQuotient_right_inv 𝒜 I)

/-- The original ideal quotient map, bundled as a degree-preserving ring map. -/
def quotientGradedMap : 𝒜 →+*ᵍ component 𝒜 I where
  __ := Ideal.Quotient.mk I.toIdeal
  map_mem := mk_mem_component 𝒜 I

theorem quotientGradedMap_surjective : Function.Surjective (quotientGradedMap 𝒜 I) :=
  Ideal.Quotient.mk_surjective

/-- The kernel is the original ideal, including all its nonreduced information. -/
theorem quotientGradedMap_ker :
    RingHom.ker (quotientGradedMap 𝒜 I).toRingHom = I.toIdeal :=
  Ideal.mk_ker

/-- Homogeneous decomposition commutes with the original quotient map. -/
theorem quotient_decompose_mk (a : A) (n : ℕ) :
    (DirectSum.decompose (component 𝒜 I) (Ideal.Quotient.mk I.toIdeal a) n :
      A ⧸ I.toIdeal) =
    Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 a n) :=
  (quotientGradedMap 𝒜 I).map_directSumDecompose.symm

/-- The scheme morphism from the Proj of the quotient into the original Proj. -/
noncomputable def projImmersion : Proj (component 𝒜 I) ⟶ Proj 𝒜 :=
  Proj.map (quotientGradedMap 𝒜 I)
    (ArithDyn.Extension.irrelevant_le_map_of_surjective _
      (quotientGradedMap_surjective 𝒜 I))

instance projImmersion_isClosedImmersion : IsClosedImmersion (projImmersion 𝒜 I) :=
  ArithDyn.Extension.proj_map_isClosedImmersion_of_surjective _
    (quotientGradedMap_surjective 𝒜 I)

/-- The actual closed immersion of the Proj of the original homogeneous ideal quotient. -/
theorem quotient_proj_isClosedImmersion :
    IsClosedImmersion (Proj.map (quotientGradedMap 𝒜 I)
      (ArithDyn.Extension.irrelevant_le_map_of_surjective _
        (quotientGradedMap_surjective 𝒜 I))) :=
  ArithDyn.Extension.proj_map_isClosedImmersion_of_surjective _
    (quotientGradedMap_surjective 𝒜 I)

end ArithDyn.Extension.GradedQuotient
