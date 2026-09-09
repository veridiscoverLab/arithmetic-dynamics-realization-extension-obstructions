import Mathlib

/-!
# Lemma 3.4 (paper §3.2): homogeneous descent along a finite separable extension

Let `K/k` be a finite separable extension with `k`-basis `β = (β_a)_{a ∈ ι}`, let `Ω ⊇ K` be an
algebraically closed field which is algebraic over `k`, and let `F = (F_i)_{i < N}` be polynomials
in `N` variables with coefficients in `K` whose only common zero in `Ω^N` is the origin.
Substituting `X_j ↦ ∑_a β_a X_{j,a}` and expanding along the basis,
`F_i(∑_a β_a X_{1,a}, …, ∑_a β_a X_{N,a}) = ∑_a β_a G_{i,a}(X)` with `G_{i,a}` polynomials over `k`
in the `N · |ι|` variables `X_{j,a}`.  We prove:

* `exists_restrictScalars`: the coordinate expansion `G` exists;
* `separable_descent_zero`: the `G_{i,a}` have only the origin as common zero in `Ω^{N × ι}`;
* `isHomogeneous_restrictScalars`: if the `F_i` are homogeneous of degree `d`, so are the `G_{i,a}`.

The proof of `separable_descent_zero` follows the paper.  Let `x` be a common zero of the `G_{i,a}`.
For each `k`-embedding `σ : K → Ω` put `z^σ_j := ∑_a σ(β_a) x_{j,a}`; applying the ring
homomorphism "`σ` on coefficients, `x` on variables" to the defining identity shows that the
conjugate system `F_i^σ` vanishes at `z^σ`.  Since `Ω/k` is algebraic and `Ω` is algebraically
closed, `σ` extends to a `k`-automorphism `τ` of `Ω`, and `F_i(τ⁻¹ z^σ) = τ⁻¹(F_i^σ(z^σ)) = 0`, so
`z^σ = 0`.  Finally the embeddings matrix `(σ(β_a))_{σ,a}` is invertible (its determinant squares to
the discriminant of `β`, which is nonzero by separability), whence `x = 0`.
-/

set_option autoImplicit false

namespace ArithDyn.Extension

open MvPolynomial
open Module (Basis)

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
  [IsScalarTower k K Ω]

/-- The substitution `X_j ↦ ∑_a β_a X_{j,a}` (coefficients in `K`). -/
noncomputable def substBasis {ι : Type*} [Fintype ι] (β : ι → K) (N : ℕ) :
    MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N × ι) K :=
  MvPolynomial.aeval (fun j : Fin N => ∑ a, MvPolynomial.C (β a) * MvPolynomial.X (j, a))

/-! ### Coordinate expansion -/

/-- Apply a `k`-linear functional to the coefficients of a polynomial over `K`. -/
noncomputable def coeffMap {τ : Type*} (f : K →ₗ[k] k) (p : MvPolynomial τ K) :
    MvPolynomial τ k :=
  ∑ m ∈ p.support, monomial m (f (coeff m p))

theorem coeff_coeffMap {τ : Type*} (f : K →ₗ[k] k) (p : MvPolynomial τ K) (m : τ →₀ ℕ) :
    coeff m (coeffMap f p) = f (coeff m p) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  by_cases h : m ∈ p.support
  · rw [if_pos h]
  · rw [if_neg h, notMem_support_iff.1 h, map_zero]

/-- Existence of the coordinate expansion `G` (ext:coordinate-expansion). -/
theorem exists_restrictScalars {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Basis ι k K) {N : ℕ}
    (F : Fin N → MvPolynomial (Fin N) K) :
    ∃ G : Fin N → ι → MvPolynomial (Fin N × ι) k, ∀ i,
      substBasis (fun a => β a) N (F i) =
        ∑ a, MvPolynomial.C (β a) * MvPolynomial.map (algebraMap k K) (G i a) := by
  refine ⟨fun i a => coeffMap (β.coord a) (substBasis (fun a => β a) N (F i)), fun i => ?_⟩
  ext m
  simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_coeffMap, Module.Basis.coord_apply]
  refine (β.sum_repr (coeff m (substBasis (fun a => β a) N (F i)))).symm.trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Algebra.smul_def, mul_comm]

/-! ### Conjugate evaluation -/

omit [Algebra K Ω] in
/-- Evaluating `substBasis β N p` at `x` with `σ` on coefficients is the same as evaluating `p`
with `σ` on coefficients at the vector `z_j = ∑_a σ (β_a) x_{j,a}`. -/
theorem eval₂_substBasis {ι : Type*} [Fintype ι] (β : ι → K) {N : ℕ} (σ : K →+* Ω)
    (x : Fin N × ι → Ω) (p : MvPolynomial (Fin N) K) :
    eval₂ σ x (substBasis β N p) = eval₂ σ (fun j => ∑ a, σ (β a) * x (j, a)) p := by
  have h : eval₂ σ x (substBasis β N p) =
      (eval₂Hom σ x) (eval₂ (algebraMap K (MvPolynomial (Fin N × ι) K))
        (fun j : Fin N => ∑ a, C (β a) * X (j, a)) p) := by
    simp only [substBasis, aeval_def, coe_eval₂Hom]
  rw [h, eval₂_comp_left]
  congr 1
  · ext c
    simp [MvPolynomial.algebraMap_eq]
  · funext j
    simp

omit [Algebra K Ω] [IsScalarTower k K Ω] in
/-- Pushing the identity `hG` through the evaluation "`σ` on coefficients, `x` on variables":
if `x` is a common zero of the `G_{i,a}`, then the conjugate system `F_i^σ` vanishes at
`z^σ_j = ∑_a σ (β_a) x_{j,a}`. -/
theorem eval₂_conj_eq_zero {ι : Type*} [Fintype ι] (β : Basis ι k K) {N : ℕ}
    (F : Fin N → MvPolynomial (Fin N) K) (G : Fin N → ι → MvPolynomial (Fin N × ι) k)
    (hG : ∀ i, substBasis (fun a => β a) N (F i) =
      ∑ a, MvPolynomial.C (β a) * MvPolynomial.map (algebraMap k K) (G i a))
    (x : Fin N × ι → Ω) (hx : ∀ i a, MvPolynomial.aeval x (G i a) = 0) (σ : K →ₐ[k] Ω)
    (i : Fin N) :
    eval₂ (σ : K →+* Ω) (fun j => ∑ a, σ (β a) * x (j, a)) (F i) = 0 := by
  have hx' : ∀ i a, eval₂ (algebraMap k Ω) x (G i a) = 0 := fun i a => by
    rw [← aeval_def]; exact hx i a
  have h := congrArg (eval₂ (σ : K →+* Ω) x) (hG i)
  rw [eval₂_substBasis] at h
  simp only [eval₂_sum, eval₂_mul, eval₂_C, eval₂_map, AlgHom.comp_algebraMap, hx', mul_zero,
    Finset.sum_const_zero, RingHom.coe_coe] at h
  exact h

/-- If the conjugate system `F^σ` vanishes at `z`, then `z = 0`: extend `σ` to a
`k`-automorphism of `Ω` and pull back to the original system. -/
theorem conj_vector_eq_zero [IsAlgClosed Ω] [Algebra.IsAlgebraic k Ω] {N : ℕ}
    (F : Fin N → MvPolynomial (Fin N) K)
    (hF : ∀ y : Fin N → Ω, (∀ i, MvPolynomial.aeval y (F i) = 0) → y = 0)
    (σ : K →ₐ[k] Ω) (z : Fin N → Ω) (hz : ∀ i, eval₂ (σ : K →+* Ω) z (F i) = 0) : z = 0 := by
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := k) K
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
    (K := k) (L := K) (M := Ω) (E := Ω) σ
  have hφ' : ∀ c, φ (algebraMap K Ω c) = σ c := fun c => AlgHom.congr_fun hφ c
  have hbij : Function.Bijective φ := Algebra.IsAlgebraic.algHom_bijective φ
  choose y hy using fun j => hbij.2 (z j)
  have hy' : ∀ i, MvPolynomial.aeval y (F i) = 0 := by
    intro i
    apply hbij.1
    rw [map_zero]
    have h := map_aeval y (φ : Ω →+* Ω) (F i)
    simp only [RingHom.coe_coe] at h
    have h1 : (φ : Ω →+* Ω).comp (algebraMap K Ω) = (σ : K →+* Ω) := RingHom.ext hφ'
    have h2 : (fun j => φ (y j)) = z := funext hy
    rw [h, h1, h2, coe_eval₂Hom]
    exact hz i
  have hy0 := hF y hy'
  funext j
  rw [← hy j, congrFun hy0 j]
  simp

/-! ### The embeddings matrix -/

omit [Algebra K Ω] [IsScalarTower k K Ω] in
/-- If `∑_a σ (β_a) v_a = 0` for every `k`-embedding `σ : K → Ω`, then `v = 0`
(the embeddings matrix of a basis of a separable extension is invertible). -/
theorem eq_zero_of_forall_embedding [FiniteDimensional k K] [Algebra.IsSeparable k K]
    [IsAlgClosed Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Basis ι k K) (v : ι → Ω)
    (hv : ∀ σ : K →ₐ[k] Ω, ∑ a, σ (β a) * v a = 0) : v = 0 := by
  have hcard : Fintype.card ι = Fintype.card (K →ₐ[k] Ω) := by
    rw [AlgHom.card k K Ω, Module.finrank_eq_card_basis β]
  let e : ι ≃ (K →ₐ[k] Ω) := Fintype.equivOfCardEq hcard
  have hdet : (Algebra.embeddingsMatrixReindex k Ω (⇑β) e).det ≠ 0 := by
    intro h
    have h2 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two k Ω (⇑β) e
    rw [h, zero_pow two_ne_zero, map_eq_zero] at h2
    exact Algebra.discr_not_zero_of_basis k β h2
  have hentry : ∀ a b, Algebra.embeddingsMatrixReindex k Ω (⇑β) e a b = (e b) (β a) := by
    intro a b
    simp [Algebra.embeddingsMatrixReindex]
  refine Matrix.eq_zero_of_vecMul_eq_zero hdet ?_
  funext b
  simp only [Matrix.vecMul, dotProduct, hentry, Pi.zero_apply]
  rw [← hv (e b)]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-! ### Main theorem -/

/-- **Lemma 3.4 (core).** If `F` has only the trivial common zero over `Ω`, so does its
restriction of scalars `G`. -/
theorem separable_descent_zero [FiniteDimensional k K] [Algebra.IsSeparable k K] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic k Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Basis ι k K) {N : ℕ}
    (F : Fin N → MvPolynomial (Fin N) K)
    (hF : ∀ y : Fin N → Ω, (∀ i, MvPolynomial.aeval y (F i) = 0) → y = 0)
    (G : Fin N → ι → MvPolynomial (Fin N × ι) k)
    (hG : ∀ i, substBasis (fun a => β a) N (F i) =
      ∑ a, MvPolynomial.C (β a) * MvPolynomial.map (algebraMap k K) (G i a))
    (x : Fin N × ι → Ω) (hx : ∀ i a, MvPolynomial.aeval x (G i a) = 0) : x = 0 := by
  have hz : ∀ σ : K →ₐ[k] Ω, ∀ j, ∑ a, σ (β a) * x (j, a) = 0 := by
    intro σ j
    have h := conj_vector_eq_zero F hF σ (fun j => ∑ a, σ (β a) * x (j, a))
      (fun i => eval₂_conj_eq_zero β F G hG x hx σ i)
    exact congrFun h j
  funext ⟨j, a⟩
  exact congrFun (eq_zero_of_forall_embedding β (fun a => x (j, a)) (fun σ => hz σ j)) a

/-! ### Homogeneity -/

/-- Substituting linear forms preserves homogeneity. -/
theorem isHomogeneous_substBasis {ι : Type*} [Fintype ι] (β : ι → K) {N : ℕ}
    (p : MvPolynomial (Fin N) K) {d : ℕ} (hp : p.IsHomogeneous d) :
    (substBasis β N p).IsHomogeneous d := by
  have h := hp.aeval (fun j : Fin N => ∑ a, C (β a) * X (j, a)) fun j =>
    IsHomogeneous.sum Finset.univ _ 1 fun a _ => isHomogeneous_C_mul_X (β a) (j, a)
  rwa [one_mul] at h

/-- A polynomial all of whose coefficients outside degree `d` vanish is homogeneous of
degree `d`. -/
theorem isHomogeneous_of_coeff_eq_zero {τ R : Type*} [CommSemiring R] (p : MvPolynomial τ R)
    {d : ℕ} (h : ∀ m : τ →₀ ℕ, m.degree ≠ d → coeff m p = 0) : p.IsHomogeneous d := by
  rw [← mem_homogeneousSubmodule, homogeneousSubmodule_eq_finsupp_supported]
  exact (Finsupp.mem_supported' _ _).2 fun m hm => h m hm

/-- Homogeneity is preserved by the coordinate expansion. -/
theorem isHomogeneous_restrictScalars {ι : Type*} [Fintype ι] [DecidableEq ι] (β : Basis ι k K)
    {N : ℕ} (F : Fin N → MvPolynomial (Fin N) K) {d : ℕ} (hF : ∀ i, (F i).IsHomogeneous d)
    (G : Fin N → ι → MvPolynomial (Fin N × ι) k)
    (hG : ∀ i, substBasis (fun a => β a) N (F i) =
      ∑ a, MvPolynomial.C (β a) * MvPolynomial.map (algebraMap k K) (G i a)) :
    ∀ i a, (G i a).IsHomogeneous d := by
  intro i a
  apply isHomogeneous_of_coeff_eq_zero
  intro m hm
  have h0 : coeff m (substBasis (fun a => β a) N (F i)) = 0 :=
    (isHomogeneous_substBasis _ _ (hF i)).coeff_eq_zero hm
  rw [hG i, coeff_sum] at h0
  simp only [coeff_C_mul, coeff_map] at h0
  have hli := Fintype.linearIndependent_iff.1 β.linearIndependent fun a => coeff m (G i a)
  refine hli ?_ a
  calc ∑ b, coeff m (G i b) • β b = ∑ b, β b * algebraMap k K (coeff m (G i b)) :=
        Finset.sum_congr rfl fun b _ => by rw [Algebra.smul_def, mul_comm]
    _ = 0 := h0

end ArithDyn.Extension
