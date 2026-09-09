import ArithDyn.Extension.Veronese

/-!
# From a single restriction-surjectivity statement to polarized coordinate lifts

Let `R` be a commutative `k`-algebra with homogeneous pieces `𝒮 n`, and let `uᵢ ∈ 𝒮 1`.
Suppose only that the restriction/evaluation map in degree `t * d` is surjective onto
`𝒮 (t * d)`.  If an algebra endomorphism `τ` sends `𝒮 t` into `𝒮 (t * d)`, then its
values on the degree-`t` Veronese coordinates have degree-`d` polynomial lifts.

The resulting polynomial substitution commutes with `τ` on the entire coordinate algebra
and preserves the actual kernel ideal, not only its radical.  Evaluation identities can
then be transported along any algebra homomorphism from `R`.

For a genuine direct-sum grading and `t > 0`, `section_restriction_kernel_isHomogeneous`
also proves that this kernel is homogeneous.  It derives that fact by projecting the
evaluation identity onto separate graded pieces.

No surjectivity in degree `t` is assumed.  No hypothesis `𝒮 0 = k` is imposed, so the
application allows disconnected and nonreduced schemes.  The graded-multiplication
assumptions are even weaker than a direct-sum grading; this does not weaken the conclusion.

For a scheme application, `R` is the section algebra and `τ` is induced by one fixed
polarization isomorphism.  This file does not assert that an arbitrary ample line bundle
has already supplied the grading, the restriction-surjectivity theorem, or the scheme
morphisms: these are the separate algebraic-geometric input and output bridges.
-/

set_option autoImplicit false

namespace ArithDyn.Extension

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- Evaluating a degree-`n` form in degree-`a` elements multiplies the degree by `a`. -/
theorem aeval_mem_graded_piece_of_degree {ι : Type*} [Fintype ι]
    (𝒮 : ℕ → Submodule k R) [SetLike.GradedMonoid 𝒮]
    {a n : ℕ} (u : ι → R) (hu : ∀ i, u i ∈ 𝒮 a)
    (p : MvPolynomial ι k) (hp : p.IsHomogeneous n) :
    aeval u p ∈ 𝒮 (a * n) := by
  classical
  conv in aeval u p => rw [p.as_sum, map_sum]
  apply (𝒮 (a * n)).sum_mem
  intro α hα
  have hαn : α.degree = n := by
    by_contra h
    exact (mem_support_iff.1 hα) (hp.coeff_eq_zero h)
  have hprod : (∏ i, u i ^ α i) ∈ 𝒮 (a * n) := by
    have h := SetLike.prod_pow_mem_graded 𝒮 (fun _ : ι => a) u α
      (F := Finset.univ) (fun i _ => hu i)
    simpa only [smul_eq_mul, ← Finset.sum_mul, ← Finsupp.degree_eq_sum, hαn,
      Nat.mul_comm n a] using h
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simpa only [Algebra.smul_def] using (𝒮 (a * n)).smul_mem (coeff α p) hprod

/-- Evaluating a homogeneous polynomial in degree-one elements respects graded pieces. -/
theorem aeval_mem_graded_piece {ι : Type*} [Fintype ι]
    (𝒮 : ℕ → Submodule k R) [SetLike.GradedMonoid 𝒮]
    (u : ι → R) (hu : ∀ i, u i ∈ 𝒮 1)
    {n : ℕ} (p : MvPolynomial ι k) (hp : p.IsHomogeneous n) :
    aeval u p ∈ 𝒮 n := by
  simpa only [one_mul] using aeval_mem_graded_piece_of_degree 𝒮 u hu p hp

/-- When the target has an actual direct-sum grading, the kernel of evaluation in
positive equal-degree sections is homogeneous.  No reducedness or injectivity of
evaluation is assumed. -/
theorem section_restriction_kernel_isHomogeneous {ι : Type*} [Fintype ι]
    (𝒮 : ℕ → Submodule k R) [GradedAlgebra 𝒮]
    {t : ℕ} (ht : 1 ≤ t) (s : ι → R) (hs : ∀ i, s i ∈ 𝒮 t) :
    (RingHom.ker (aeval s : MvPolynomial ι k →ₐ[k] R)).IsHomogeneous
      (homogeneousSubmodule ι k) := by
  classical
  intro n p hp
  rw [RingHom.mem_ker] at hp ⊢
  have hdec : ((DirectSum.decompose (homogeneousSubmodule ι k) p n :
      homogeneousSubmodule ι k n) : MvPolynomial ι k) = homogeneousComponent n p :=
    decomposition.decompose'_apply p n
  rw [hdec]
  have hcomp : ∀ m, aeval s (homogeneousComponent m p) ∈ 𝒮 (t * m) :=
    fun m => aeval_mem_graded_piece_of_degree 𝒮 s hs _ (homogeneousComponent_isHomogeneous m p)
  have hsum : aeval s p = ∑ m ∈ Finset.range (p.totalDegree + 1),
      aeval s (homogeneousComponent m p) := by
    rw [← map_sum, sum_homogeneousComponent]
  have key : GradedRing.proj 𝒮 (t * n) (aeval s p) =
      aeval s (homogeneousComponent n p) := by
    rw [hsum, map_sum, Finset.sum_eq_single n]
    · exact DirectSum.decompose_of_mem_same 𝒮 (hcomp n)
    · intro m _ hmn
      exact DirectSum.decompose_of_mem_ne 𝒮 (hcomp m)
        (fun h => hmn (Nat.eq_of_mul_eq_mul_left (by omega) h))
    · intro hn
      have hlt : p.totalDegree < n := by
        simp only [Finset.mem_range, not_lt] at hn
        omega
      rw [homogeneousComponent_eq_zero n p hlt, map_zero, map_zero]
  rw [← key, hp, map_zero]

/-- The degree-`t` Veronese coordinates in a general graded algebra lie in its `t`-th piece. -/
theorem veronese_sections_mem (𝒮 : ℕ → Submodule k R) [SetLike.GradedMonoid 𝒮]
    {r : ℕ} (u : Fin (r + 1) → R) (hu : ∀ i, u i ∈ 𝒮 1)
    (t : ℕ) (α : VerIdx r t) :
    aeval u (verMon (k := k) r t α) ∈ 𝒮 t :=
  aeval_mem_graded_piece 𝒮 u hu _ (verMon_isHomogeneous r t α)

/-- Restriction of a polynomial in the new coordinates is restriction after Veronese
substitution in the old polynomial ring. -/
theorem aeval_veronese_sections {r t : ℕ} (u : Fin (r + 1) → R)
    (G : MvPolynomial (VerIdx r t) k) :
    aeval (fun α => aeval u (verMon (k := k) r t α)) G =
      aeval u (aeval (verMon (k := k) r t) G) := by
  rw [comp_aeval_apply]

/-- A single surjectivity statement in degree `t * d` yields lifts of any family in that
piece.  In particular, no restriction-surjectivity hypothesis in degree `t` is used. -/
theorem exists_lifts_of_veronese_restriction_surjective
    {r t d : ℕ} (u : Fin (r + 1) → R) (T : Submodule k R)
    (hres : ∀ x ∈ T, ∃ p : MvPolynomial (Fin (r + 1)) k,
      p.IsHomogeneous (t * d) ∧ aeval u p = x)
    {η : Type*} (x : η → R) (hx : ∀ i, x i ∈ T) :
    ∃ F : η → MvPolynomial (VerIdx r t) k,
      (∀ i, (F i).IsHomogeneous d) ∧
      (∀ i, aeval (fun α => aeval u (verMon (k := k) r t α)) (F i) = x i) := by
  classical
  have hlift : ∀ i, ∃ G : MvPolynomial (VerIdx r t) k, G.IsHomogeneous d ∧
      aeval (fun α => aeval u (verMon (k := k) r t α)) G = x i := by
    intro i
    obtain ⟨p, hp, hpx⟩ := hres (x i) (hx i)
    obtain ⟨G, hG, hGp⟩ := exists_rewrite_verMon r t d p hp
    refine ⟨G, hG, ?_⟩
    rw [aeval_veronese_sections, hGp, hpx]
  choose F hF hFx using hlift
  exact ⟨F, hF, hFx⟩

/-- Coordinate identities imply a commuting square on all polynomials, not merely on
geometric points. -/
theorem coordinate_lifts_commute {ν : Type*} (s : ν → R) (τ : R →ₐ[k] R)
    (F : ν → MvPolynomial ν k) (hF : ∀ i, aeval s (F i) = τ (s i)) :
    (aeval s).comp (aeval F) = τ.comp (aeval s) := by
  ext i
  simpa only [AlgHom.comp_apply, aeval_X] using hF i

/-- A coordinate lift preserves the actual kernel of the restriction map.  This is the
ideal-preservation hypothesis required for the existing polynomial extension and iterate
theorems, and retains nilpotent information. -/
theorem coordinate_lifts_preserve_kernel {ν : Type*} (s : ν → R) (τ : R →ₐ[k] R)
    (F : ν → MvPolynomial ν k) (hF : ∀ i, aeval s (F i) = τ (s i)) :
    ∀ g ∈ RingHom.ker (aeval s : MvPolynomial ν k →ₐ[k] R),
      aeval F g ∈ RingHom.ker (aeval s : MvPolynomial ν k →ₐ[k] R) := by
  intro g hg
  rw [RingHom.mem_ker] at hg ⊢
  have h := AlgHom.congr_fun (coordinate_lifts_commute s τ F hF) g
  simpa only [AlgHom.comp_apply, hg, map_zero] using h

/-- Pulling the coordinate identity through an arbitrary algebra homomorphism gives the
corresponding pointwise evaluation identity.  Scheme/fibre interpretations are separate. -/
theorem evaluate_coordinate_lifts {ν K : Type*} [CommRing K] [Algebra k K]
    (s : ν → R) (τ : R →ₐ[k] R) (F : ν → MvPolynomial ν k)
    (hF : ∀ i, aeval s (F i) = τ (s i)) (χ : R →ₐ[k] K) (i : ν) :
    aeval (fun j => χ (s j)) (F i) = χ (τ (s i)) := by
  rw [← comp_aeval_apply, hF]

/-- Nonvanishing of a pulled-back coordinate is preserved by its exact polynomial lift. -/
theorem coordinate_lifts_nonvanishing {ν K : Type*} [CommRing K] [Algebra k K]
    (s : ν → R) (τ : R →ₐ[k] R) (F : ν → MvPolynomial ν k)
    (hF : ∀ i, aeval s (F i) = τ (s i)) (χ : R →ₐ[k] K)
    (h : ∃ i, χ (τ (s i)) ≠ 0) :
    ∃ i, aeval (fun j => χ (s j)) (F i) ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by rwa [evaluate_coordinate_lifts s τ F hF χ]⟩

/-- The algebraic input bridge for a polarized section algebra.  Surjectivity is assumed
only in degree `t * d`; the degree-`t` coordinates are the restrictions of all Veronese
monomials.  The conclusion includes exact coordinate identities and preservation of the
original restriction kernel. -/
theorem exists_polarized_veronese_coordinate_lifts
    (𝒮 : ℕ → Submodule k R) [SetLike.GradedMonoid 𝒮]
    {r t d : ℕ} (u : Fin (r + 1) → R) (hu : ∀ i, u i ∈ 𝒮 1)
    (τ : R →ₐ[k] R) (hτ : ∀ x ∈ 𝒮 t, τ x ∈ 𝒮 (t * d))
    (hres : ∀ x ∈ 𝒮 (t * d), ∃ p : MvPolynomial (Fin (r + 1)) k,
      p.IsHomogeneous (t * d) ∧ aeval u p = x) :
    let s : VerIdx r t → R := fun α => aeval u (verMon (k := k) r t α)
    ∃ F : VerIdx r t → MvPolynomial (VerIdx r t) k,
      (∀ α, (F α).IsHomogeneous d) ∧
      (∀ α, aeval s (F α) = τ (s α)) ∧
      (aeval s).comp (aeval F) = τ.comp (aeval s) ∧
      (∀ g ∈ RingHom.ker (aeval s : MvPolynomial (VerIdx r t) k →ₐ[k] R),
        aeval F g ∈ RingHom.ker (aeval s : MvPolynomial (VerIdx r t) k →ₐ[k] R)) := by
  dsimp only
  obtain ⟨F, hFd, hF⟩ := exists_lifts_of_veronese_restriction_surjective u (𝒮 (t * d))
    hres (fun α => τ (aeval u (verMon (k := k) r t α)))
    (fun α => hτ _ (veronese_sections_mem 𝒮 u hu t α))
  exact ⟨F, hFd, hF, coordinate_lifts_commute _ τ F hF,
    coordinate_lifts_preserve_kernel _ τ F hF⟩

/-- The same input bridge with the homogeneous-kernel condition supplied from an actual
grading.  Together with geometric nonvanishing, these are the algebraic inputs of the
existing polynomial extension core. -/
theorem exists_polarized_lifts_with_homogeneous_kernel
    (𝒮 : ℕ → Submodule k R) [GradedAlgebra 𝒮]
    {r t d : ℕ} (ht : 1 ≤ t) (u : Fin (r + 1) → R) (hu : ∀ i, u i ∈ 𝒮 1)
    (τ : R →ₐ[k] R) (hτ : ∀ x ∈ 𝒮 t, τ x ∈ 𝒮 (t * d))
    (hres : ∀ x ∈ 𝒮 (t * d), ∃ p : MvPolynomial (Fin (r + 1)) k,
      p.IsHomogeneous (t * d) ∧ aeval u p = x) :
    let s : VerIdx r t → R := fun α => aeval u (verMon (k := k) r t α)
    let I := RingHom.ker (aeval s : MvPolynomial (VerIdx r t) k →ₐ[k] R)
    I.IsHomogeneous (homogeneousSubmodule (VerIdx r t) k) ∧
    ∃ F : VerIdx r t → MvPolynomial (VerIdx r t) k,
      (∀ α, (F α).IsHomogeneous d) ∧
      (∀ α, aeval s (F α) = τ (s α)) ∧
      (aeval s).comp (aeval F) = τ.comp (aeval s) ∧
      (∀ g ∈ I, aeval F g ∈ I) := by
  refine ⟨section_restriction_kernel_isHomogeneous 𝒮 ht _
    (veronese_sections_mem 𝒮 u hu t), ?_⟩
  exact exists_polarized_veronese_coordinate_lifts 𝒮 u hu τ hτ hres

end ArithDyn.Extension
