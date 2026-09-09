import ArithDyn.Extension.Veronese
import ArithDyn.Extension.Avoidance

/-!
# Core of Theorem 3.1: extending a base-point-free system to the Veronese ambient space

Let `k` be a field, `S = k[u₀, …, u_r]`, `I ⊆ S` a homogeneous ideal whose geometric projective
zero set `X ⊆ ℙ^r(Ω)` (`Ω` algebraically closed) is nonempty, and let `f₀, …, f_r ∈ S_d`
(`d ≥ 2`) have no common zero on `X`.  Let `t ≥ 1` be such that `X` is cut out by elements of `I`
of degree `≤ t`.  Passing to the degree-`t` Veronese coordinates `Y_α` (`α ∈ VerIdx r t`) and to
an infinite intermediate field `k ⊆ κ ⊆ Ω`, we produce forms `F_α ∈ κ[Y]_d` **without common zero
in `Ω^{VerIdx} ∖ {0}`** such that `F_α(u^β) ≡ verMon_α(f) (mod I κ[u])`.

The construction is the one of the paper (§3, Lemma 3.2 and Lemma 3.3): with
`ρ : κ[Y] → κ[u]`, `Y_α ↦ u^α`, `J := ρ⁻¹(I_κ)` and `V := J ∩ κ[Y]_d`, choose `F⁰_α ∈ κ[Y]_d`
with `ρ(F⁰_α) = verMon_α(f)` (`exists_rewrite_verMon`) and perturb inside `V` by prime avoidance
(`exists_add_mem_radical`), whose hypothesis is checked with the Nullstellensatz through
Lemma 3.2(3) (`exists_mem_V_ne_zero_or_mem_image`): a nonzero point of `Ω^{VerIdx}` either lies
on the Veronese image of `X` or is separated from it by an element of `V`.

## Main statements

* `projZeros Ω I`: the nonzero geometric vectors on which every element of `I` vanishes.
* `exists_mem_V_ne_zero_or_mem_image` (Lemma 3.2(3)).
* `exists_add_mem_radical_of_fintype`: `exists_add_mem_radical` transported from `Fin n` to an
  arbitrary finite index type along `renameEquiv`.
* `exists_extension_core`: the core of Theorem 3.1 over `κ`.
-/

set_option autoImplicit false

namespace ArithDyn.Extension

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {r : ℕ}

/-- Geometric points (nonzero vectors) of the projective zero set of `I`. -/
def projZeros (Ω : Type*) [Field Ω] [Algebra k Ω] (I : Ideal (MvPolynomial (Fin (r + 1)) k)) :
    Set (Fin (r + 1) → Ω) :=
  {v | v ≠ 0 ∧ ∀ g ∈ I, aeval v g = 0}

/-- The affine Veronese map `v ↦ (v^α)_α`. -/
def verMap (r t : ℕ) {Ω : Type*} [CommSemiring Ω] (v : Fin (r + 1) → Ω) : VerIdx r t → Ω :=
  fun α => ∏ i, v i ^ α.1 i

/-! ### Generic lemmas on homogeneous polynomials -/

/-- Scaling a form of degree `n`: `φ(c • w) = c ^ n * φ(w)`. -/
theorem aeval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {R A : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A] {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsHomogeneous n)
    (c : A) (w : σ → A) :
    aeval (c • w) φ = c ^ n * aeval w φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i, m i = n := by
    rw [← Finsupp.degree_eq_sum]
    by_contra h
    exact mem_support_iff.1 hm (hφ.coeff_eq_zero h)
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- Evaluating `G` at the Veronese point `verMap v` is evaluating `ρ G` at `v`. -/
theorem aeval_verMap {κ Ω : Type*} [CommRing κ] [CommRing Ω] [Algebra κ Ω] (r t : ℕ)
    (v : Fin (r + 1) → Ω) (G : MvPolynomial (VerIdx r t) κ) :
    aeval (verMap r t v) G = aeval v (aeval (verMon (k := κ) r t) G) := by
  rw [comp_aeval_apply]
  have h : (fun β => aeval v (verMon (k := κ) r t β)) = verMap r t v :=
    funext fun β => aeval_verMon r t β v
  rw [h]

/-- Elements of `I_κ = I · κ[u]` vanish at the geometric points of `X`. -/
theorem aeval_eq_zero_of_mem_map {κ Ω : Type*} [Field κ] [Field Ω] [Algebra k κ] [Algebra k Ω]
    [Algebra κ Ω] [IsScalarTower k κ Ω] {I : Ideal (MvPolynomial (Fin (r + 1)) k)}
    {v : Fin (r + 1) → Ω} (hv : v ∈ projZeros Ω I) {p : MvPolynomial (Fin (r + 1)) κ}
    (hp : p ∈ I.map (MvPolynomial.map (algebraMap k κ))) : aeval v p = 0 := by
  have hle : I.map (MvPolynomial.map (algebraMap k κ)) ≤
      RingHom.ker (aeval v : MvPolynomial (Fin (r + 1)) κ →ₐ[κ] Ω) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, aeval_map_algebraMap]
    exact hv.2 g hg
  exact RingHom.mem_ker.1 (hle hp)

/-! ### Homogeneous ideals: images and preimages -/

/-- The image of a homogeneous ideal under a ring hom sending forms to forms of the same degree
is homogeneous. -/
theorem isHomogeneous_map_of_forall {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]
    {F : Type*} [FunLike F (MvPolynomial σ R) (MvPolynomial τ S)]
    [RingHomClass F (MvPolynomial σ R) (MvPolynomial τ S)] (e : F)
    (he : ∀ (x : MvPolynomial σ R) (n : ℕ), x.IsHomogeneous n → (e x).IsHomogeneous n)
    {I : Ideal (MvPolynomial σ R)} (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) :
    (I.map e).IsHomogeneous (homogeneousSubmodule τ S) := by
  obtain ⟨T, hT⟩ :=
    (Ideal.IsHomogeneous.iff_exists (𝒜 := homogeneousSubmodule σ R) (I := I)).1 hI
  rw [hT, Ideal.map_span]
  refine Ideal.homogeneous_span _ _ ?_
  rintro _ ⟨_, ⟨⟨x, n, hx⟩, -, rfl⟩, rfl⟩
  exact ⟨n, (mem_homogeneousSubmodule _ _).2 (he x n ((mem_homogeneousSubmodule _ _).1 hx))⟩

/-- Membership in the image of an ideal under an algebra equivalence. -/
theorem mem_map_algEquiv_iff {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (I : Ideal A) (y : B) :
    y ∈ I.map e ↔ e.symm y ∈ I := by
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).1 hy
    rwa [AlgEquiv.symm_apply_apply]
  · intro hy
    have h := Ideal.mem_map_of_mem e hy
    rwa [AlgEquiv.apply_symm_apply] at h

/-- The preimage under `ρ : κ[Y] → κ[u]`, `Y_α ↦ u^α`, of a homogeneous ideal is homogeneous
(`ρ` multiplies degrees by `t`). -/
theorem isHomogeneous_comap_aeval_verMon {κ : Type*} [Field κ] {t : ℕ} (ht : 1 ≤ t)
    {I' : Ideal (MvPolynomial (Fin (r + 1)) κ)}
    (hI' : I'.IsHomogeneous (homogeneousSubmodule (Fin (r + 1)) κ)) :
    (I'.comap (aeval (verMon (k := κ) r t) :
      MvPolynomial (VerIdx r t) κ →ₐ[κ] MvPolynomial (Fin (r + 1)) κ)).IsHomogeneous
        (homogeneousSubmodule (VerIdx r t) κ) := by
  intro n G hG
  rw [Ideal.mem_comap] at hG ⊢
  have hdec : ((DirectSum.decompose (homogeneousSubmodule (VerIdx r t) κ) G n :
      homogeneousSubmodule (VerIdx r t) κ n) : MvPolynomial (VerIdx r t) κ) =
      homogeneousComponent n G :=
    decomposition.decompose'_apply G n
  rw [hdec]
  have hcomp : ∀ m,
      (aeval (verMon (k := κ) r t) (homogeneousComponent m G)).IsHomogeneous (t * m) :=
    fun m => (homogeneousComponent_isHomogeneous m G).aeval _ (fun β => verMon_isHomogeneous r t β)
  have hsum : aeval (verMon (k := κ) r t) G = ∑ m ∈ Finset.range (G.totalDegree + 1),
      aeval (verMon (k := κ) r t) (homogeneousComponent m G) := by
    rw [← map_sum, sum_homogeneousComponent]
  have key : homogeneousComponent (t * n) (aeval (verMon (k := κ) r t) G) =
      aeval (verMon (k := κ) r t) (homogeneousComponent n G) := by
    rw [hsum, map_sum, Finset.sum_eq_single n]
    · rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 (hcomp n)), if_pos rfl]
    · intro m _ hmn
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 (hcomp m)), if_neg]
      intro h
      exact hmn (Nat.eq_of_mul_eq_mul_left (by omega) h).symm
    · intro hn
      have hlt : G.totalDegree < n := by
        simp only [Finset.mem_range, not_lt] at hn
        omega
      rw [homogeneousComponent_eq_zero n G hlt, map_zero, map_zero]
  rw [← key]
  have h := hI' (t * n) hG
  have hdec' : ((DirectSum.decompose (homogeneousSubmodule (Fin (r + 1)) κ)
      (aeval (verMon (k := κ) r t) G) (t * n) :
      homogeneousSubmodule (Fin (r + 1)) κ (t * n)) : MvPolynomial (Fin (r + 1)) κ) =
      homogeneousComponent (t * n) (aeval (verMon (k := κ) r t) G) :=
    decomposition.decompose'_apply _ _
  rwa [hdec'] at h

/-! ### Prime avoidance over an arbitrary finite index type -/

/-- `exists_add_mem_radical`, transported from `Fin n` to an arbitrary finite index type `σ`
along `renameEquiv κ (Fintype.equivFin σ)`. -/
theorem exists_add_mem_radical_of_fintype {κ : Type*} [Field κ] [Infinite κ] {σ : Type*}
    [Fintype σ] (J : Ideal (MvPolynomial σ κ)) (hJ : J.IsHomogeneous (homogeneousSubmodule σ κ))
    (hJne : J ≠ ⊤) (V : Submodule κ (MvPolynomial σ κ)) (hVJ : ∀ v ∈ V, v ∈ J)
    (hV : ∀ P : Ideal (MvPolynomial σ κ), P.IsPrime → P.IsHomogeneous (homogeneousSubmodule σ κ) →
      ¬ J ≤ P → ¬ (∀ v ∈ V, v ∈ P))
    (F₀ : σ → MvPolynomial σ κ) (d : ℕ) (hF₀ : ∀ i, (F₀ i).IsHomogeneous d)
    (hVd : ∀ v ∈ V, v.IsHomogeneous d) :
    ∃ F : σ → MvPolynomial σ κ, (∀ i, F i - F₀ i ∈ V) ∧
      J ≤ (Ideal.span (Set.range F)).radical := by
  classical
  obtain ⟨f⟩ : Nonempty (σ ≃ Fin (Fintype.card σ)) := ⟨Fintype.equivFin σ⟩
  obtain ⟨ε, hε, hεs⟩ : ∃ ε : MvPolynomial σ κ ≃ₐ[κ] MvPolynomial (Fin (Fintype.card σ)) κ,
      (∀ x, ε x = rename f x) ∧ (∀ y, ε.symm y = rename f.symm y) :=
    ⟨renameEquiv κ f, fun _ => rfl, fun _ => rfl⟩
  have hhom : ∀ (x : MvPolynomial σ κ) (m : ℕ), x.IsHomogeneous m → (ε x).IsHomogeneous m :=
    fun x m hx => by rw [hε]; exact hx.rename_isHomogeneous
  have hhom' : ∀ (y : MvPolynomial (Fin (Fintype.card σ)) κ) (m : ℕ), y.IsHomogeneous m →
      (ε.symm y).IsHomogeneous m :=
    fun y m hy => by rw [hεs]; exact hy.rename_isHomogeneous
  -- the transported subspace
  obtain ⟨V', hV'⟩ : ∃ V' : Submodule κ (MvPolynomial (Fin (Fintype.card σ)) κ),
      ∀ y, y ∈ V' ↔ ε.symm y ∈ V :=
    ⟨V.comap ε.symm.toLinearMap, fun y => Iff.rfl⟩
  have hJ'ne : J.map ε ≠ ⊤ := by
    intro htop
    apply hJne
    rw [Ideal.eq_top_iff_one] at htop ⊢
    have h := (mem_map_algEquiv_iff ε J 1).1 htop
    rwa [map_one] at h
  have hV'J : ∀ v ∈ V', v ∈ J.map ε :=
    fun v hv => (mem_map_algEquiv_iff ε J v).2 (hVJ _ ((hV' v).1 hv))
  have hV'P : ∀ P' : Ideal (MvPolynomial (Fin (Fintype.card σ)) κ), P'.IsPrime →
      P'.IsHomogeneous (homogeneousSubmodule (Fin (Fintype.card σ)) κ) → ¬ J.map ε ≤ P' →
      ¬ (∀ v ∈ V', v ∈ P') := by
    intro P' hP' hP'hom hJP' hVP'
    have hPeq : Ideal.comap ε P' = P'.map ε.symm := Ideal.ext fun x => by
      rw [Ideal.mem_comap, mem_map_algEquiv_iff, AlgEquiv.symm_symm]
    have hPprime : (Ideal.comap ε P').IsPrime := by
      haveI := hP'
      infer_instance
    have hPhom : (Ideal.comap ε P').IsHomogeneous (homogeneousSubmodule σ κ) := by
      rw [hPeq]
      exact isHomogeneous_map_of_forall ε.symm hhom' hP'hom
    refine hV _ hPprime hPhom (fun h => hJP' (Ideal.map_le_iff_le_comap.2 h)) fun v hv => ?_
    rw [Ideal.mem_comap]
    refine hVP' _ ((hV' _).2 ?_)
    rw [AlgEquiv.symm_apply_apply]
    exact hv
  have hV'd : ∀ v ∈ V', v.IsHomogeneous d := by
    intro v hv
    have h := hhom _ _ (hVd _ ((hV' v).1 hv))
    rwa [AlgEquiv.apply_symm_apply] at h
  obtain ⟨F', hF'V, hF'J⟩ := exists_add_mem_radical (J.map ε)
    (isHomogeneous_map_of_forall ε hhom hJ) hJ'ne V' hV'J hV'P (fun i => ε (F₀ (f.symm i))) d
    (fun i => hhom _ _ (hF₀ _)) hV'd
  refine ⟨fun j => ε.symm (F' (f j)), fun j => ?_, ?_⟩
  · have h := (hV' _).1 (hF'V (f j))
    rwa [map_sub, AlgEquiv.symm_apply_apply, Equiv.symm_apply_apply] at h
  · intro g hg
    have hg' := hF'J ((mem_map_algEquiv_iff ε J (ε g)).2 (by
      rw [AlgEquiv.symm_apply_apply]; exact hg))
    obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.1 hg'
    refine Ideal.mem_radical_iff.2 ⟨m, ?_⟩
    have hrange : Set.range F' = ε '' Set.range (fun j => ε.symm (F' (f j))) := by
      rw [← Set.range_comp]
      have h : (ε ∘ fun j => ε.symm (F' (f j))) = F' ∘ f := by
        funext j
        simp
      rw [h, f.surjective.range_comp]
    rw [hrange, ← Ideal.map_span] at hm
    have h := (mem_map_algEquiv_iff ε _ _).1 hm
    rwa [← map_pow, AlgEquiv.symm_apply_apply] at h

/-! ### Lemma 3.2(3): points of the Veronese ambient space -/

/-- **Lemma 3.2(3).** A nonzero point `w` of `Ω^{VerIdx}` either is a scalar multiple of the
Veronese image of a geometric point of `X`, or is separated from the Veronese image of `X` by a
form `G ∈ V`, i.e. a form of degree `d` with `ρ G ∈ I_κ` and `G(w) ≠ 0`. -/
theorem exists_mem_V_ne_zero_or_mem_image {κ Ω : Type*} [Field κ] [Field Ω] [Algebra k κ]
    [Algebra k Ω] [Algebra κ Ω] [IsScalarTower k κ Ω]
    (I : Ideal (MvPolynomial (Fin (r + 1)) k)) (t : ℕ) (ht : 1 ≤ t)
    (hgen : ∀ v : Fin (r + 1) → Ω, v ≠ 0 → v ∉ projZeros Ω I →
      ∃ g ∈ I, ∃ e ≤ t, g.IsHomogeneous e ∧ aeval v g ≠ 0)
    (d : ℕ) (hd : 2 ≤ d) (w : VerIdx r t → Ω) (hw : w ≠ 0) :
    (∃ v ∈ projZeros Ω I, ∃ c : Ω, c ≠ 0 ∧ w = c • verMap r t v) ∨
    (∃ G : MvPolynomial (VerIdx r t) κ, G.IsHomogeneous d ∧
      aeval (verMon (k := κ) r t) G ∈ I.map (MvPolynomial.map (algebraMap k κ)) ∧
      aeval w G ≠ 0) := by
  classical
  obtain ⟨α₀, hα₀⟩ : ∃ α₀, w α₀ ≠ 0 := Function.ne_iff.1 hw
  by_cases hquad : ∀ α β γ δ : VerIdx r t, α.1 + β.1 = γ.1 + δ.1 → w α * w β = w γ * w δ
  · -- `w` satisfies the quadric relations: it is a Veronese point
    obtain ⟨v, c, hv0, hc, hwv⟩ := exists_verMap_of_quadrics r t ht w hw hquad
    have hw' : w = c • verMap r t v := funext fun α => hwv α
    by_cases hvX : v ∈ projZeros Ω I
    · exact Or.inl ⟨v, hvX, c, hc, hw'⟩
    right
    obtain ⟨g, hgI, e, het, hge, hgv⟩ := hgen v hv0 hvX
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv0
    -- `g' = g * uᵢ^(t - e) ∈ I` is a form of degree `t`, hence `ρ` of a linear form `G₁`
    have hg'I : g * X i ^ (t - e) ∈ I := I.mul_mem_right _ hgI
    have hg' : (MvPolynomial.map (algebraMap k κ) (g * X i ^ (t - e))).IsHomogeneous (t * 1) := by
      have h := (hge.mul ((isHomogeneous_X k i).pow (t - e))).map (algebraMap k κ)
      rw [mul_one]
      convert h using 1
      omega
    obtain ⟨G₁, hG₁hom, hG₁⟩ := exists_rewrite_verMon r t 1 _ hg'
    have hG₁w : aeval w G₁ = c * aeval v (g * X i ^ (t - e)) := by
      rw [hw', aeval_smul_of_isHomogeneous hG₁hom, pow_one, aeval_verMap, hG₁,
        aeval_map_algebraMap]
    refine ⟨G₁ * X α₀ ^ (d - 1), ?_, ?_, ?_⟩
    · have h := hG₁hom.mul ((isHomogeneous_X κ α₀).pow (d - 1))
      convert h using 1
      omega
    · rw [map_mul, hG₁]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hg'I)
    · rw [map_mul, map_pow, aeval_X, hG₁w, map_mul, map_pow, aeval_X]
      exact mul_ne_zero (mul_ne_zero hc (mul_ne_zero hgv (pow_ne_zero _ hi))) (pow_ne_zero _ hα₀)
  · -- `w` violates a quadric relation `Y_α Y_β - Y_γ Y_δ`, which lies in `J`
    right
    push Not at hquad
    obtain ⟨α, β, γ, δ, hsum, hne⟩ := hquad
    refine ⟨(X α * X β - X γ * X δ) * X α₀ ^ (d - 2), ?_, ?_, ?_⟩
    · have h := (((isHomogeneous_X κ α).mul (isHomogeneous_X κ β)).sub
        ((isHomogeneous_X κ γ).mul (isHomogeneous_X κ δ))).mul ((isHomogeneous_X κ α₀).pow (d - 2))
      convert h using 1
      omega
    · simp only [map_mul, map_sub, aeval_X]
      have h : verMon (k := κ) r t α * verMon r t β = verMon r t γ * verMon r t δ := by
        simp only [verMon, monomial_mul, mul_one, hsum]
      rw [h, sub_self, zero_mul]
      exact Ideal.zero_mem _
    · simp only [map_mul, map_sub, map_pow, aeval_X]
      exact mul_ne_zero (sub_ne_zero.2 hne) (pow_ne_zero _ hα₀)

/-! ### The core of Theorem 3.1 -/

set_option maxHeartbeats 800000 in
/-- **Core of Theorem 3.1** (over an infinite field `κ`, `k ⊆ κ ⊆ Ω`). -/
theorem exists_extension_core {κ Ω : Type*} [Field κ] [Field Ω] [Algebra k κ] [Algebra k Ω]
    [Algebra κ Ω] [IsScalarTower k κ Ω] [Infinite κ] [IsAlgClosed Ω]
    (I : Ideal (MvPolynomial (Fin (r + 1)) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (r + 1)) k))
    (t : ℕ) (ht : 1 ≤ t)
    (hgen : ∀ v : Fin (r + 1) → Ω, v ≠ 0 → v ∉ projZeros Ω I →
      ∃ g ∈ I, ∃ e ≤ t, g.IsHomogeneous e ∧ aeval v g ≠ 0)
    (hX : (projZeros Ω I).Nonempty)
    (d : ℕ) (hd : 2 ≤ d) (f : Fin (r + 1) → MvPolynomial (Fin (r + 1)) k)
    (hf : ∀ i, (f i).IsHomogeneous d)
    (hbase : ∀ v ∈ projZeros Ω I, ∃ i, aeval v (f i) ≠ 0) :
    ∃ F : VerIdx r t → MvPolynomial (VerIdx r t) κ,
      (∀ α, (F α).IsHomogeneous d) ∧
      (∀ w : VerIdx r t → Ω, w ≠ 0 → ∃ α, aeval w (F α) ≠ 0) ∧
      (∀ α, aeval (fun β => MvPolynomial.map (algebraMap k κ) (verMon r t β)) (F α) -
        MvPolynomial.map (algebraMap k κ) (aeval f (verMon (k := k) r t α)) ∈
          I.map (MvPolynomial.map (algebraMap k κ))) := by
  classical
  -- the Veronese monomials over `κ`
  have hM : (fun β => MvPolynomial.map (algebraMap k κ) (verMon (k := k) r t β)) =
      verMon (k := κ) r t := by
    funext β
    simp only [verMon, map_monomial, map_one]
  rw [hM]
  -- notation: `I_κ`, `ρ`, `J = ρ⁻¹(I_κ)`
  obtain ⟨Iκ, hIκ⟩ : ∃ Iκ : Ideal (MvPolynomial (Fin (r + 1)) κ),
      Iκ = I.map (MvPolynomial.map (algebraMap k κ)) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : MvPolynomial (VerIdx r t) κ →ₐ[κ] MvPolynomial (Fin (r + 1)) κ,
      ρ = aeval (verMon (k := κ) r t) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : Ideal (MvPolynomial (VerIdx r t) κ), J = Iκ.comap ρ := ⟨_, rfl⟩
  have hJmem : ∀ G, G ∈ J ↔ ρ G ∈ Iκ := fun G => by rw [hJ, Ideal.mem_comap]
  have hkill : ∀ v ∈ projZeros Ω I, ∀ p ∈ Iκ, aeval v p = 0 := by
    intro v hv p hp
    rw [hIκ] at hp
    exact aeval_eq_zero_of_mem_map hv hp
  have hIκhom : Iκ.IsHomogeneous (homogeneousSubmodule (Fin (r + 1)) κ) := by
    rw [hIκ]
    exact isHomogeneous_map_of_forall (MvPolynomial.map (algebraMap k κ))
      (fun x n hx => hx.map _) hI
  have hIκne : Iκ ≠ ⊤ := by
    obtain ⟨v, hv⟩ := hX
    intro htop
    have h := hkill v hv 1 ((Ideal.eq_top_iff_one _).1 htop)
    rw [map_one] at h
    exact one_ne_zero h
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (VerIdx r t) κ) := by
    rw [hJ, hρ]
    exact isHomogeneous_comap_aeval_verMon ht hIκhom
  have hJne : J ≠ ⊤ := by
    intro htop
    apply hIκne
    rw [Ideal.eq_top_iff_one] at htop ⊢
    have h := (hJmem 1).1 htop
    rwa [map_one] at h
  -- the subspace `V = J ∩ κ[Y]_d`
  obtain ⟨V, hV⟩ : ∃ V : Submodule κ (MvPolynomial (VerIdx r t) κ),
      ∀ G, G ∈ V ↔ G ∈ J ∧ G.IsHomogeneous d :=
    ⟨J.restrictScalars κ ⊓ homogeneousSubmodule (VerIdx r t) κ d, fun G => by
      rw [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_homogeneousSubmodule]⟩
  -- (i) the common zeros of `V` are the Veronese points of `X`
  have hzero : ∀ w : VerIdx r t → Ω, w ≠ 0 → (∀ G ∈ V, aeval w G = 0) →
      ∃ v ∈ projZeros Ω I, ∃ c : Ω, c ≠ 0 ∧ w = c • verMap r t v := by
    intro w hw hwV
    rcases exists_mem_V_ne_zero_or_mem_image (κ := κ) I t ht hgen d hd w hw with
      h | ⟨G, hGd, hGI, hGw⟩
    · exact h
    · refine absurd (hwV G ((hV G).2 ⟨(hJmem G).2 ?_, hGd⟩)) hGw
      rw [hρ, hIκ]
      exact hGI
  -- (ii) the avoidance hypothesis, by the Nullstellensatz
  have hVP : ∀ P : Ideal (MvPolynomial (VerIdx r t) κ), P.IsPrime →
      P.IsHomogeneous (homogeneousSubmodule (VerIdx r t) κ) → ¬ J ≤ P →
      ¬ (∀ v ∈ V, v ∈ P) := by
    intro P hP hPhom hJP hVP'
    apply hJP
    intro g hg
    have hdec : g = ∑ n ∈ Finset.range (g.totalDegree + 1), homogeneousComponent n g :=
      (sum_homogeneousComponent g).symm
    rw [hdec]
    refine Ideal.sum_mem _ fun n _ => ?_
    have hnJ : homogeneousComponent n g ∈ J := by
      have h1 := hJhom n hg
      have h2 : ((DirectSum.decompose (homogeneousSubmodule (VerIdx r t) κ) g n :
          homogeneousSubmodule (VerIdx r t) κ n) : MvPolynomial (VerIdx r t) κ) =
          homogeneousComponent n g :=
        decomposition.decompose'_apply g n
      rwa [h2] at h1
    have hnhom : (homogeneousComponent n g).IsHomogeneous n :=
      homogeneousComponent_isHomogeneous n g
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- degree `0`: the constant term of an element of the proper ideal `J` is zero
      rw [homogeneousComponent_zero] at hnJ ⊢
      by_cases h0 : coeff 0 g = 0
      · rw [h0, map_zero]
        exact P.zero_mem
      · exact absurd (Ideal.eq_top_of_isUnit_mem J hnJ ((isUnit_iff_ne_zero.2 h0).map C)) hJne
    · -- positive degree: vanishing on `zeroLocus Ω P`
      rw [← hP.radical, ← vanishingIdeal_zeroLocus_eq_radical (K := Ω) P, mem_vanishingIdeal_iff]
      intro w hw
      rw [mem_zeroLocus_iff] at hw
      by_cases hw0 : w = 0
      · subst hw0
        have h := aeval_smul_of_isHomogeneous hnhom (0 : Ω) (0 : VerIdx r t → Ω)
        rwa [zero_smul, zero_pow (by omega), zero_mul] at h
      · obtain ⟨v, hvX, c, hc, hwv⟩ := hzero w hw0 fun G hG => hw G (hVP' G hG)
        rw [hwv, aeval_smul_of_isHomogeneous hnhom, aeval_verMap, ← hρ,
          hkill v hvX _ ((hJmem _).1 hnJ), mul_zero]
  -- the forms `F₀ α` lifting `verMon α (f)`
  have hF₀ex : ∀ α : VerIdx r t, ∃ F₀ : MvPolynomial (VerIdx r t) κ, F₀.IsHomogeneous d ∧
      ρ F₀ = MvPolynomial.map (algebraMap k κ) (aeval f (verMon (k := k) r t α)) := by
    intro α
    have h : (MvPolynomial.map (algebraMap k κ)
        (aeval f (verMon (k := k) r t α))).IsHomogeneous (t * d) := by
      have h' := ((verMon_isHomogeneous (k := k) r t α).aeval f hf).map (algebraMap k κ)
      rwa [mul_comm] at h'
    obtain ⟨F₀, hF₀hom, hF₀⟩ := exists_rewrite_verMon r t d _ h
    exact ⟨F₀, hF₀hom, by rw [hρ]; exact hF₀⟩
  choose F₀ hF₀hom hF₀ρ using hF₀ex
  -- prime avoidance
  obtain ⟨F, hFV, hFJ⟩ := exists_add_mem_radical_of_fintype J hJhom hJne V
    (fun v hv => ((hV v).1 hv).1) hVP F₀ d hF₀hom (fun v hv => ((hV v).1 hv).2)
  have hFhom : ∀ α, (F α).IsHomogeneous d := by
    intro α
    have h : F α = F₀ α + (F α - F₀ α) := by ring
    rw [h]
    exact (hF₀hom α).add ((hV _).1 (hFV α)).2
  have hFρ : ∀ α, ρ (F α) - MvPolynomial.map (algebraMap k κ) (aeval f (verMon (k := k) r t α)) ∈ Iκ := by
    intro α
    rw [← hF₀ρ α, ← map_sub]
    exact (hJmem _).1 ((hV _).1 (hFV α)).1
  refine ⟨F, hFhom, ?_, fun α => by rw [← hρ, ← hIκ]; exact hFρ α⟩
  -- (iii) base-point-freeness
  intro w hw
  by_contra hcon
  push Not at hcon
  have hrad : ∀ G ∈ (Ideal.span (Set.range F)).radical, aeval w G = 0 := by
    intro G hG
    obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.1 hG
    have hspan : Ideal.span (Set.range F) ≤
        RingHom.ker (aeval w : MvPolynomial (VerIdx r t) κ →ₐ[κ] Ω) := by
      rw [Ideal.span_le]
      rintro _ ⟨α, rfl⟩
      exact RingHom.mem_ker.2 (hcon α)
    have h := RingHom.mem_ker.1 (hspan hm)
    rw [map_pow] at h
    exact (pow_eq_zero_iff'.1 h).1
  obtain ⟨v, hvX, c, hc, hwv⟩ := hzero w hw fun G hG => hrad G (hFJ ((hV G).1 hG).1)
  have hcomp : ∀ α, aeval w (F α) = c ^ d * ∏ i, (aeval v (f i)) ^ α.1 i := by
    intro α
    rw [hwv, aeval_smul_of_isHomogeneous (hFhom α), aeval_verMap, ← hρ]
    congr 1
    have h1 : ρ (F α) = MvPolynomial.map (algebraMap k κ) (aeval f (verMon (k := k) r t α)) +
        (ρ (F α) - MvPolynomial.map (algebraMap k κ) (aeval f (verMon (k := k) r t α))) := by ring
    rw [h1, map_add, hkill v hvX _ (hFρ α), add_zero, aeval_map_algebraMap, comp_aeval_apply,
      aeval_verMon]
  obtain ⟨i, hi⟩ := hbase v hvX
  apply hi
  obtain ⟨αi, hαi⟩ : ∃ αi : VerIdx r t, αi.1 = Finsupp.single i t :=
    ⟨⟨_, Finsupp.degree_single i t⟩, rfl⟩
  have h := hcon αi
  rw [hcomp, hαi] at h
  have h2 : ∏ j, (aeval v (f j)) ^ (Finsupp.single i t : Fin (r + 1) →₀ ℕ) j =
      (aeval v (f i)) ^ t := by
    rw [Finset.prod_eq_single i]
    · rw [Finsupp.single_eq_same]
    · intro j _ hj
      rw [Finsupp.single_eq_of_ne hj, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h2] at h
  rcases mul_eq_zero.1 h with h3 | h3
  · exact absurd ((pow_eq_zero_iff (by omega)).1 h3) hc
  · exact (pow_eq_zero_iff (by omega)).1 h3

end ArithDyn.Extension
