import ArithDyn.Extension.QuotientDynamics
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# A semantic regression on the nonreduced dual point

In `k[ε]/(ε²)`, the class of `ε` is nonzero but has square zero.  Substituting `ε`
and substituting `0` therefore induce different algebra endomorphisms, even though
their composites with every field-valued point agree.  This checks that the quotient
dynamics construction retains the original nonreduced structure rather than passing
to its radical or to its geometric points.
-/

set_option autoImplicit false

namespace ArithDyn.Extension.NilpotentRegression

open MvPolynomial

variable (k : Type*) [Field k]

/-- The unreduced ideal `(ε²)`. -/
noncomputable def dualIdeal : Ideal (MvPolynomial Unit k) :=
  Ideal.span {(X () : MvPolynomial Unit k) ^ 2}

/-- The infinitesimal class in the original quotient. -/
noncomputable def epsilon : MvPolynomial Unit k ⧸ dualIdeal k :=
  Ideal.Quotient.mk (dualIdeal k) (X ())

theorem epsilon_sq_zero : epsilon k ^ 2 = 0 := by
  have h : (X () : MvPolynomial Unit k) ^ 2 ∈ dualIdeal k :=
    Ideal.subset_span (Set.mem_singleton _)
  simpa only [epsilon, map_pow] using (Ideal.Quotient.eq_zero_iff_mem.2 h)

/-- A concrete square-zero extension witnesses that `ε` was not killed. -/
theorem epsilon_ne_zero : epsilon k ≠ 0 := by
  let e : TrivSqZeroExt k k := TrivSqZeroExt.inr 1
  let φ : MvPolynomial Unit k →ₐ[k] TrivSqZeroExt k k := aeval (fun _ => e)
  have hker : dualIdeal k ≤ RingHom.ker φ.toRingHom := by
    apply Ideal.span_le.2
    intro g hg
    obtain rfl := Set.mem_singleton_iff.1 hg
    simp [φ, e, pow_two]
  let ψ : (MvPolynomial Unit k ⧸ dualIdeal k) →ₐ[k] TrivSqZeroExt k k :=
    Ideal.Quotient.liftₐ (dualIdeal k) φ (fun g hg => RingHom.mem_ker.1 (hker hg))
  intro h
  have he : e = 0 := by
    have h' := congrArg ψ h
    simpa [ψ, epsilon, φ] using h'
  have h1 := congrArg TrivSqZeroExt.snd he
  change (1 : k) = 0 at h1
  exact one_ne_zero h1

theorem identity_preserves :
    ∀ g ∈ dualIdeal k, aeval (X : Unit → MvPolynomial Unit k) g ∈ dualIdeal k := by
  intro g hg
  simpa using hg

theorem zero_preserves :
    ∀ g ∈ dualIdeal k, aeval (fun _ : Unit => (0 : MvPolynomial Unit k)) g ∈ dualIdeal k := by
  let φ : MvPolynomial Unit k →ₐ[k] MvPolynomial Unit k := aeval (fun _ => 0)
  have hker : dualIdeal k ≤ RingHom.ker φ.toRingHom := by
    apply Ideal.span_le.2
    intro g hg
    obtain rfl := Set.mem_singleton_iff.1 hg
    simp [φ]
  intro g hg
  have hg0 := RingHom.mem_ker.1 (hker hg)
  rw [show aeval (fun _ : Unit => (0 : MvPolynomial Unit k)) g = 0 from hg0]
  exact Ideal.zero_mem _

noncomputable def identityEnd : (MvPolynomial Unit k ⧸ dualIdeal k) →ₐ[k]
    (MvPolynomial Unit k ⧸ dualIdeal k) :=
  quotientEnd (dualIdeal k) X (identity_preserves k)

noncomputable def zeroEnd : (MvPolynomial Unit k ⧸ dualIdeal k) →ₐ[k]
    (MvPolynomial Unit k ⧸ dualIdeal k) :=
  quotientEnd (dualIdeal k) (fun _ => 0) (zero_preserves k)

theorem identityEnd_eq_id : identityEnd k = AlgHom.id k (MvPolynomial Unit k ⧸ dualIdeal k) := by
  apply AlgHom.ext
  intro x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  change quotientEnd (dualIdeal k) X (identity_preserves k) (Ideal.Quotient.mk _ g) =
    Ideal.Quotient.mk _ g
  rw [quotientEnd_mk]
  simp

@[simp] theorem identityEnd_epsilon : identityEnd k (epsilon k) = epsilon k := by
  simp [identityEnd, epsilon]

@[simp] theorem zeroEnd_epsilon : zeroEnd k (epsilon k) = 0 := by
  simp [zeroEnd, epsilon]

/-- Distinct endomorphisms of the actual nonreduced coordinate algebra. -/
theorem quotient_endomorphisms_distinct : identityEnd k ≠ zeroEnd k := by
  intro h
  have he := AlgHom.congr_fun h (epsilon k)
  simp only [identityEnd_epsilon, zeroEnd_epsilon] at he
  exact epsilon_ne_zero k he

/-- Faithfulness of `Spec` retains the distinction as actual scheme morphisms. -/
theorem spectrum_endomorphisms_distinct :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (identityEnd k).toRingHom) ≠
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (zeroEnd k).toRingHom) := by
  intro h
  have hr := AlgebraicGeometry.Spec.map_injective h
  apply quotient_endomorphisms_distinct k
  apply AlgHom.ext
  intro x
  exact congrArg (fun f : CommRingCat.of (MvPolynomial Unit k ⧸ dualIdeal k) ⟶
    CommRingCat.of (MvPolynomial Unit k ⧸ dualIdeal k) => f.hom x) hr

/-- Every field-valued point kills the infinitesimal class. -/
theorem field_point_epsilon {K : Type*} [Field K] [Algebra k K]
    (x : (MvPolynomial Unit k ⧸ dualIdeal k) →ₐ[k] K) : x (epsilon k) = 0 := by
  have h : x (epsilon k) ^ 2 = 0 := by rw [← map_pow, epsilon_sq_zero, map_zero]
  exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).1 h

/-- The two distinct maps are indistinguishable on all field-valued points, hence also
on all geometric points over an algebraic closure. -/
theorem same_on_all_field_points {K : Type*} [Field K] [Algebra k K]
    (x : (MvPolynomial Unit k ⧸ dualIdeal k) →ₐ[k] K) :
    x.comp (identityEnd k) = x.comp (zeroEnd k) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro a
  cases a
  change x (identityEnd k (epsilon k)) = x (zeroEnd k (epsilon k))
  rw [identityEnd_epsilon, zeroEnd_epsilon, map_zero]
  exact field_point_epsilon k x

end ArithDyn.Extension.NilpotentRegression
