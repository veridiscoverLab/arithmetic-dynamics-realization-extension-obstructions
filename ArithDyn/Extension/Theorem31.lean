import ArithDyn.Extension.ExtendCore
import ArithDyn.Extension.SeparableDescent

/-!
# Theorem 3.1 (concrete form): extension of a polarized self-map to the ambient space

Let `k` be a field, `X = V(I) ⊆ ℙ^r_k` a nonempty projective scheme (`I` homogeneous), and let
`φ : X → X` be given by forms `f₀, …, f_r` of degree `d ≥ 2` without common zero on `X`
(so `φ^* O_X(1) = O_X(d)`).  We show that after re-embedding `X` by a Veronese-type map
`j : X ↪ ℙ(ν)` (given by forms of degree `s ≥ 1`, base-point-free on `X` and generating the
Veronese subring), `φ` extends to an endomorphism `Ψ` of `ℙ(ν)` of the same degree `d`, without
base points, with `Ψ ∘ j = j ∘ φ` on `X` (i.e. `Ψ_m(j) ≡ j_m(f) mod I`).

The proof follows §3 of the paper.

* `exists_extension_core'` refines `exists_extension_core`: the correction terms added to the
  `k`-rational lifts `F₀ α` of `verMon_α(f)` are `κ`-linear combinations of finitely many
  **`k`-rational** forms `G ∈ S` of degree `d` with `ρ(G) ∈ I` (`ρ : Y_α ↦ u^α`).  This is
  obtained by running the prime-avoidance argument of `exists_extension_core` with the subspace
  `V = J ∩ κ[Y]_d` replaced by the `κ`-span `W` of the `k`-rational elements of `V`; the
  Nullstellensatz step only needs the `k`-rational form of Lemma 3.2(3)
  (`exists_mem_V_ne_zero_or_mem_image_k`).
* `theorem_3_1`: if `k` is infinite, take `κ = k`.  If `k` is finite, take `κ = Ω = k̄`; the
  finitely many coefficients `ω α G ∈ Ω` generate a finite (separable, `k` being perfect)
  extension `K₀/k`, and Lemma 3.4 (`separable_descent_zero`) descends the system `F` from `K₀`
  to `k` by restriction of scalars along a `k`-basis of `K₀`.  The compatibility `Ψ ∘ j = j ∘ φ`
  is recovered from the defining identity of the restriction of scalars by comparing coefficients
  along the basis (`eq_of_sum_C_mul_map_eq`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ArithDyn.Extension

open MvPolynomial
open Module (Basis)

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {r : ℕ}

/-! ### Generic lemmas: `aeval` versus `map` -/

/-- The Veronese monomials are defined over the prime field. -/
theorem map_verMon {κ : Type*} [CommRing κ] [Algebra k κ] (r t : ℕ) (α : VerIdx r t) :
    MvPolynomial.map (algebraMap k κ) (verMon (k := k) r t α) = verMon (k := κ) r t α := by
  simp only [verMon, map_monomial, map_one]

/-- Extension of scalars commutes with substitution of polynomials. -/
theorem map_aeval_eq {σ τ : Type*} {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (j : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    MvPolynomial.map (algebraMap R A) (aeval j p) =
      aeval (fun m => MvPolynomial.map (algebraMap R A) (j m)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, hp]

/-- `ρ_κ (G ⊗ 1) = ρ_k (G) ⊗ 1` for a `k`-rational form `G`. -/
theorem aeval_verMon_map {κ : Type*} [Field κ] [Algebra k κ] (r t : ℕ)
    (G : MvPolynomial (VerIdx r t) k) :
    aeval (verMon (k := κ) r t) (MvPolynomial.map (algebraMap k κ) G) =
      MvPolynomial.map (algebraMap k κ) (aeval (verMon (k := k) r t) G) := by
  rw [aeval_map_algebraMap, map_aeval_eq]
  have h : (fun β => MvPolynomial.map (algebraMap k κ) (verMon (k := k) r t β)) =
      verMon (k := κ) r t := funext (map_verMon r t)
  rw [h]

/-- Evaluation of the Veronese monomial `u_i^t`. -/
theorem aeval_verMon_single {K : Type*} [CommRing K] [Algebra k K] (r t : ℕ) (i : Fin (r + 1))
    (v : Fin (r + 1) → K) :
    aeval v (verMon (k := k) r t ⟨Finsupp.single i t, Finsupp.degree_single i t⟩) = v i ^ t := by
  rw [aeval_verMon]
  show ∏ j, v j ^ (Finsupp.single i t : Fin (r + 1) →₀ ℕ) j = v i ^ t
  rw [Finset.prod_eq_single i]
  · rw [Finsupp.single_eq_same]
  · intro j _ hj
    rw [Finsupp.single_eq_of_ne hj, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Homogeneous components of elements of a homogeneous ideal lie in the ideal. -/
theorem homogeneousComponent_mem_of_isHomogeneous {σ : Type*}
    {I : Ideal (MvPolynomial σ k)} (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    {g : MvPolynomial σ k} (hg : g ∈ I) (n : ℕ) : homogeneousComponent n g ∈ I := by
  have h1 := hI n hg
  have h2 : ((DirectSum.decompose (homogeneousSubmodule σ k) g n :
      homogeneousSubmodule σ k n) : MvPolynomial σ k) = homogeneousComponent n g :=
    decomposition.decompose'_apply g n
  rwa [h2] at h1

/-! ### Lemma 3.2(3), `k`-rational form -/

/-- **Lemma 3.2(3), `k`-rational form.** A nonzero point `w` of `Ω^{VerIdx}` either is a scalar
multiple of the Veronese image of a geometric point of `X`, or is separated from the Veronese image
of `X` by a **`k`-rational** form `G` of degree `d` with `ρ G ∈ I`. -/
theorem exists_mem_V_ne_zero_or_mem_image_k {Ω : Type*} [Field Ω] [Algebra k Ω]
    (I : Ideal (MvPolynomial (Fin (r + 1)) k)) (t : ℕ) (ht : 1 ≤ t)
    (hgen : ∀ v : Fin (r + 1) → Ω, v ≠ 0 → v ∉ projZeros Ω I →
      ∃ g ∈ I, ∃ e ≤ t, g.IsHomogeneous e ∧ aeval v g ≠ 0)
    (d : ℕ) (hd : 2 ≤ d) (w : VerIdx r t → Ω) (hw : w ≠ 0) :
    (∃ v ∈ projZeros Ω I, ∃ c : Ω, c ≠ 0 ∧ w = c • verMap r t v) ∨
    (∃ G : MvPolynomial (VerIdx r t) k, G.IsHomogeneous d ∧
      aeval (verMon (k := k) r t) G ∈ I ∧ aeval w G ≠ 0) := by
  rcases exists_mem_V_ne_zero_or_mem_image (κ := k) I t ht hgen d hd w hw with
    h | ⟨G, hGd, hGI, hGw⟩
  · exact Or.inl h
  · refine Or.inr ⟨G, hGd, ?_, hGw⟩
    have hid : MvPolynomial.map (algebraMap k k) = RingHom.id (MvPolynomial (Fin (r + 1)) k) :=
      RingHom.ext fun p => by rw [Algebra.algebraMap_self, MvPolynomial.map_id, RingHom.id_apply]
    rwa [hid, Ideal.map_id] at hGI

/-! ### The refined core: `k`-rational correction terms -/

set_option maxHeartbeats 1600000 in
/-- **Core of Theorem 3.1, refined.** The forms `F α = F₀ α + ∑_{G ∈ S} ω α G • G` have no common
zero in `Ω^{VerIdx} ∖ {0}`, where `F₀ α ∈ k[Y]_d` lifts `verMon_α(f)` and the `G ∈ S ⊆ k[Y]_d`
satisfy `ρ G ∈ I` (over `k`). -/
theorem exists_extension_core' {κ Ω : Type*} [Field κ] [Field Ω] [Algebra k κ] [Algebra k Ω]
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
    ∃ (F₀ : VerIdx r t → MvPolynomial (VerIdx r t) k) (S : Finset (MvPolynomial (VerIdx r t) k))
      (ω : VerIdx r t → MvPolynomial (VerIdx r t) k → κ),
      (∀ α, (F₀ α).IsHomogeneous d ∧
        aeval (verMon r t) (F₀ α) = aeval f (verMon (k := k) r t α)) ∧
      (∀ G ∈ S, G.IsHomogeneous d ∧ aeval (verMon r t) G ∈ I) ∧
      (∀ w : VerIdx r t → Ω, w ≠ 0 → ∃ α,
        aeval w (MvPolynomial.map (algebraMap k κ) (F₀ α) +
          ∑ G ∈ S, C (ω α G) * MvPolynomial.map (algebraMap k κ) G) ≠ 0) := by
  classical
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
  -- `ρ` of a `k`-rational form
  have hρmap : ∀ G : MvPolynomial (VerIdx r t) k,
      ρ (MvPolynomial.map (algebraMap k κ) G) =
        MvPolynomial.map (algebraMap k κ) (aeval (verMon (k := k) r t) G) := by
    intro G
    rw [hρ]
    exact aeval_verMon_map r t G
  -- the `k`-rational generators of `W`
  obtain ⟨gen, hgen'⟩ : ∃ gen : {G : MvPolynomial (VerIdx r t) k //
      G.IsHomogeneous d ∧ aeval (verMon (k := k) r t) G ∈ I} → MvPolynomial (VerIdx r t) κ,
      ∀ G, gen G = MvPolynomial.map (algebraMap k κ) (G : MvPolynomial (VerIdx r t) k) :=
    ⟨fun G => MvPolynomial.map (algebraMap k κ) (G : MvPolynomial (VerIdx r t) k), fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Submodule κ (MvPolynomial (VerIdx r t) κ),
      W = Submodule.span κ (Set.range gen) := ⟨_, rfl⟩
  have hgenJ : ∀ G, gen G ∈ J := by
    intro G
    rw [hJmem, hgen', hρmap, hIκ]
    exact Ideal.mem_map_of_mem _ G.2.2
  have hgenhom : ∀ G, (gen G).IsHomogeneous d := by
    intro G
    rw [hgen']
    exact G.2.1.map _
  have hWJ : ∀ v ∈ W, v ∈ J := by
    intro v hv
    rw [hW] at hv
    have hle : Submodule.span κ (Set.range gen) ≤ J.restrictScalars κ := by
      rw [Submodule.span_le]
      rintro _ ⟨G, rfl⟩
      exact hgenJ G
    exact hle hv
  have hWd : ∀ v ∈ W, v.IsHomogeneous d := by
    intro v hv
    rw [hW] at hv
    have hle : Submodule.span κ (Set.range gen) ≤ homogeneousSubmodule (VerIdx r t) κ d := by
      rw [Submodule.span_le]
      rintro _ ⟨G, rfl⟩
      exact (mem_homogeneousSubmodule _ _).2 (hgenhom G)
    exact (mem_homogeneousSubmodule _ _).1 (hle hv)
  -- (i) the common zeros of the generators of `W` are the Veronese points of `X`
  have hzero : ∀ w : VerIdx r t → Ω, w ≠ 0 → (∀ G, aeval w (gen G) = 0) →
      ∃ v ∈ projZeros Ω I, ∃ c : Ω, c ≠ 0 ∧ w = c • verMap r t v := by
    intro w hw hwV
    rcases exists_mem_V_ne_zero_or_mem_image_k I t ht hgen d hd w hw with
      h | ⟨G, hGd, hGI, hGw⟩
    · exact h
    · refine absurd ?_ hGw
      have h := hwV ⟨G, hGd, hGI⟩
      rwa [hgen', aeval_map_algebraMap] at h
  -- (ii) the avoidance hypothesis, by the Nullstellensatz
  have hWP : ∀ P : Ideal (MvPolynomial (VerIdx r t) κ), P.IsPrime →
      P.IsHomogeneous (homogeneousSubmodule (VerIdx r t) κ) → ¬ J ≤ P →
      ¬ (∀ v ∈ W, v ∈ P) := by
    intro P hP hPhom hJP hWP'
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
      · obtain ⟨v, hvX, c, hc, hwv⟩ := hzero w hw0 fun G => hw (gen G)
          (hWP' (gen G) (by rw [hW]; exact Submodule.subset_span ⟨G, rfl⟩))
        rw [hwv, aeval_smul_of_isHomogeneous hnhom, aeval_verMap, ← hρ,
          hkill v hvX _ ((hJmem _).1 hnJ), mul_zero]
  -- the `k`-rational forms `F₀ α` lifting `verMon α (f)`
  have hF₀ex : ∀ α : VerIdx r t, ∃ F₀ : MvPolynomial (VerIdx r t) k, F₀.IsHomogeneous d ∧
      aeval (verMon (k := k) r t) F₀ = aeval f (verMon (k := k) r t α) := by
    intro α
    have h : (aeval f (verMon (k := k) r t α)).IsHomogeneous (t * d) := by
      have h' := (verMon_isHomogeneous (k := k) r t α).aeval f hf
      rwa [mul_comm] at h'
    exact exists_rewrite_verMon r t d _ h
  choose F₀ hF₀hom hF₀ρ using hF₀ex
  -- prime avoidance
  obtain ⟨F, hFW, hFJ⟩ := exists_add_mem_radical_of_fintype J hJhom hJne W hWJ hWP
    (fun α => MvPolynomial.map (algebraMap k κ) (F₀ α)) d (fun α => (hF₀hom α).map _) hWd
  have hFhom : ∀ α, (F α).IsHomogeneous d := by
    intro α
    have h : F α = MvPolynomial.map (algebraMap k κ) (F₀ α) +
        (F α - MvPolynomial.map (algebraMap k κ) (F₀ α)) := by ring
    rw [h]
    exact ((hF₀hom α).map _).add (hWd _ (hFW α))
  have hFρ : ∀ α, ρ (F α) -
      MvPolynomial.map (algebraMap k κ) (aeval f (verMon (k := k) r t α)) ∈ Iκ := by
    intro α
    rw [← hF₀ρ α, ← hρmap, ← map_sub]
    exact (hJmem _).1 (hWJ _ (hFW α))
  -- (iii) base-point-freeness of `F`
  have hbpf : ∀ w : VerIdx r t → Ω, w ≠ 0 → ∃ α, aeval w (F α) ≠ 0 := by
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
    obtain ⟨v, hvX, c, hc, hwv⟩ := hzero w hw fun G => hrad (gen G) (hFJ (hgenJ G))
    have hcomp : ∀ α, aeval w (F α) = c ^ d * ∏ i, (aeval v (f i)) ^ α.1 i := by
      intro α
      rw [hwv, aeval_smul_of_isHomogeneous (hFhom α), aeval_verMap, ← hρ]
      congr 1
      have h1 : ρ (F α) = MvPolynomial.map (algebraMap k κ) (aeval f (verMon (k := k) r t α)) +
          (ρ (F α) - MvPolynomial.map (algebraMap k κ) (aeval f (verMon (k := k) r t α))) := by
        ring
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
  -- unpack `F α - F₀ α ⊗ 1 ∈ W` into finite combinations of the generators
  have hFW' : ∀ α, ∃ c : {G : MvPolynomial (VerIdx r t) k //
      G.IsHomogeneous d ∧ aeval (verMon (k := k) r t) G ∈ I} →₀ κ,
      (c.sum fun G a => a • gen G) = F α - MvPolynomial.map (algebraMap k κ) (F₀ α) := by
    intro α
    have h := hFW α
    rw [hW] at h
    exact Finsupp.mem_span_range_iff_exists_finsupp.1 h
  choose cf hcf using hFW'
  obtain ⟨S, hS⟩ : ∃ S : Finset (MvPolynomial (VerIdx r t) k),
      S = Finset.univ.biUnion fun α => (cf α).support.image Subtype.val := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω : VerIdx r t → MvPolynomial (VerIdx r t) k → κ,
      ∀ α G, ω α G = if h : G.IsHomogeneous d ∧ aeval (verMon (k := k) r t) G ∈ I then
        cf α ⟨G, h⟩ else 0 := ⟨_, fun _ _ => rfl⟩
  refine ⟨F₀, S, ω, fun α => ⟨hF₀hom α, hF₀ρ α⟩, ?_, ?_⟩
  · intro G hG
    rw [hS, Finset.mem_biUnion] at hG
    obtain ⟨α, -, hG⟩ := hG
    rw [Finset.mem_image] at hG
    obtain ⟨G', -, rfl⟩ := hG
    exact G'.2
  · intro w hw
    obtain ⟨α, hα⟩ := hbpf w hw
    refine ⟨α, ?_⟩
    have hsub : (cf α).support.image Subtype.val ⊆ S := by
      rw [hS]
      exact Finset.subset_biUnion_of_mem (fun α => (cf α).support.image Subtype.val)
        (Finset.mem_univ α)
    have hsum : ∑ G ∈ S, C (ω α G) * MvPolynomial.map (algebraMap k κ) G =
        F α - MvPolynomial.map (algebraMap k κ) (F₀ α) := by
      rw [← hcf α, Finsupp.sum, ← Finset.sum_subset hsub, Finset.sum_image]
      · refine Finset.sum_congr rfl fun G' _ => ?_
        rw [hω, dif_pos G'.2, hgen', smul_eq_C_mul]
      · intro x _ y _ hxy
        exact Subtype.ext hxy
      · intro G _ hG
        rw [hω]
        split_ifs with h
        · have hnot : (⟨G, h⟩ : {G : MvPolynomial (VerIdx r t) k //
              G.IsHomogeneous d ∧ aeval (verMon (k := k) r t) G ∈ I}) ∉ (cf α).support := by
            intro hmem
            exact hG (Finset.mem_image_of_mem Subtype.val hmem)
          rw [Finsupp.notMem_support_iff.1 hnot, map_zero, zero_mul]
        · rw [map_zero, zero_mul]
    rw [hsum, add_sub_cancel]
    exact hα

/-! ### Theorem 3.1: preliminaries -/

/-- Choice of the degree bound `t`: if `I = (T)` and all elements of `T` have total degree `≤ t`,
then `X` is cut out by the homogeneous elements of `I` of degree `≤ t`. -/
theorem hgen_of_span {Ω : Type*} [Field Ω] [Algebra k Ω]
    (I : Ideal (MvPolynomial (Fin (r + 1)) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (r + 1)) k))
    (T : Finset (MvPolynomial (Fin (r + 1)) k)) (hT : Ideal.span (T : Set _) = I) (t : ℕ)
    (ht : ∀ g ∈ T, g.totalDegree ≤ t) :
    ∀ v : Fin (r + 1) → Ω, v ≠ 0 → v ∉ projZeros Ω I →
      ∃ g ∈ I, ∃ e ≤ t, g.IsHomogeneous e ∧ aeval v g ≠ 0 := by
  intro v hv hvX
  -- some generator does not vanish at `v`
  obtain ⟨g, hgT, hgv⟩ : ∃ g ∈ T, aeval v g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hvX
    show v ≠ 0 ∧ ∀ g ∈ I, aeval v g = 0
    refine ⟨hv, fun g hg => ?_⟩
    have hle : I ≤ RingHom.ker (aeval v : MvPolynomial (Fin (r + 1)) k →ₐ[k] Ω) := by
      rw [← hT, Ideal.span_le]
      intro g hg
      exact RingHom.mem_ker.2 (hcon g hg)
    exact RingHom.mem_ker.1 (hle hg)
  have hgI : g ∈ I := by
    rw [← hT]
    exact Ideal.subset_span hgT
  -- some homogeneous component of `g` does not vanish at `v`
  have hdec : aeval v g =
      ∑ n ∈ Finset.range (g.totalDegree + 1), aeval v (homogeneousComponent n g) := by
    rw [← map_sum, sum_homogeneousComponent]
  rw [hdec] at hgv
  obtain ⟨n, hn, hnv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hgv
  refine ⟨homogeneousComponent n g, homogeneousComponent_mem_of_isHomogeneous hI hgI n, n, ?_,
    homogeneousComponent_isHomogeneous n g, hnv⟩
  rw [Finset.mem_range] at hn
  exact (Nat.lt_succ_iff.1 hn).trans (ht g hgT)

/-- Expanding a coefficient `x ∈ K` along a `k`-basis: `∑_b β_b · (repr x)_b · p = x · p`. -/
theorem sum_C_mul_map_C_repr_mul {K : Type*} [Field K] [Algebra k K] {ι : Type*} [Fintype ι]
    (β : Basis ι k K) (x : K) {σ : Type*} (p : MvPolynomial σ k) :
    ∑ b, C (β b) * MvPolynomial.map (algebraMap k K) (C (β.repr x b) * p) =
      C x * MvPolynomial.map (algebraMap k K) p := by
  have h : ∀ b, C (β b) * MvPolynomial.map (algebraMap k K) (C (β.repr x b) * p) =
      C (β.repr x b • β b) * MvPolynomial.map (algebraMap k K) p := by
    intro b
    rw [map_mul, map_C, ← mul_assoc, ← C_mul, Algebra.smul_def, mul_comm (β b)]
  simp only [h]
  rw [← Finset.sum_mul, ← map_sum C (fun b => β.repr x b • β b) Finset.univ, β.sum_repr]

/-- Comparing coefficients along a `k`-basis of `K`: if `∑_b β_b · h_b = ∑_b β_b · h'_b` in
`K[X]` with `h_b, h'_b ∈ k[X]`, then `h = h'`. -/
theorem eq_of_sum_C_mul_map_eq {K : Type*} [Field K] [Algebra k K] {ι : Type*} [Fintype ι]
    (β : Basis ι k K) {σ : Type*} (h h' : ι → MvPolynomial σ k)
    (heq : ∑ b, C (β b) * MvPolynomial.map (algebraMap k K) (h b) =
      ∑ b, C (β b) * MvPolynomial.map (algebraMap k K) (h' b)) : h = h' := by
  funext a
  ext m
  have hc := congrArg (coeff m) heq
  simp only [coeff_sum, coeff_C_mul, coeff_map] at hc
  have hli := Fintype.linearIndependent_iff.1 β.linearIndependent
    (fun b => coeff m (h b) - coeff m (h' b)) ?_ a
  · exact sub_eq_zero.1 hli
  · simp only [Algebra.smul_def, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact (Finset.sum_congr rfl fun b _ => mul_comm _ _).trans
      (hc.trans (Finset.sum_congr rfl fun b _ => mul_comm _ _))

/-! ### Theorem 3.1: the case of an infinite field -/

/-- Theorem 3.1 over an infinite field: no descent is needed. -/
theorem theorem_3_1_of_infinite [Infinite k] (I : Ideal (MvPolynomial (Fin (r + 1)) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (r + 1)) k))
    (t : ℕ) (ht : 1 ≤ t)
    (hgen : ∀ v : Fin (r + 1) → AlgebraicClosure k, v ≠ 0 →
      v ∉ projZeros (AlgebraicClosure k) I →
      ∃ g ∈ I, ∃ e ≤ t, g.IsHomogeneous e ∧ aeval v g ≠ 0)
    (hX : (projZeros (AlgebraicClosure k) I).Nonempty)
    (d : ℕ) (hd : 2 ≤ d) (f : Fin (r + 1) → MvPolynomial (Fin (r + 1)) k)
    (hf : ∀ i, (f i).IsHomogeneous d)
    (hbase : ∀ v ∈ projZeros (AlgebraicClosure k) I, ∃ i, aeval v (f i) ≠ 0) :
    ∃ (ν : Type) (_ : Fintype ν) (s : ℕ) (j : ν → MvPolynomial (Fin (r + 1)) k)
      (Ψ : ν → MvPolynomial ν k),
      1 ≤ s ∧
      (∀ m, (j m).IsHomogeneous s) ∧
      (∀ v ∈ projZeros (AlgebraicClosure k) I, ∃ m, aeval v (j m) ≠ 0) ∧
      (∀ (n : ℕ) (g : MvPolynomial (Fin (r + 1)) k), g.IsHomogeneous (n * s) →
        ∃ G : MvPolynomial ν k, G.IsHomogeneous n ∧ aeval j G = g) ∧
      (∀ m, (Ψ m).IsHomogeneous d) ∧
      (∀ w : ν → AlgebraicClosure k, w ≠ 0 → ∃ m, aeval w (Ψ m) ≠ 0) ∧
      (∀ m, aeval j (Ψ m) - aeval f (j m) ∈ I) := by
  obtain ⟨F₀, S, ω, hF₀, hS, hbpf⟩ :=
    exists_extension_core' (κ := k) (Ω := AlgebraicClosure k) I hI t ht hgen hX d hd f hf hbase
  refine ⟨VerIdx r t, inferInstance, t, verMon r t,
    fun α => F₀ α + ∑ G ∈ S, C (ω α G) * G, ht, verMon_isHomogeneous r t, ?_, ?_, ?_, ?_, ?_⟩
  · -- `j` has no base point on `X`
    intro v hv
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv.1
    refine ⟨⟨Finsupp.single i t, Finsupp.degree_single i t⟩, ?_⟩
    rw [aeval_verMon_single]
    exact pow_ne_zero _ hi
  · -- `j` generates the Veronese subring
    intro n g hg
    exact exists_rewrite_verMon r t n g (by rwa [mul_comm])
  · -- `Ψ` is homogeneous of degree `d`
    intro α
    exact (hF₀ α).1.add (IsHomogeneous.sum _ _ _ fun G hG => (hS G hG).1.C_mul _)
  · -- `Ψ` has no base point
    intro w hw
    obtain ⟨α, hα⟩ := hbpf w hw
    refine ⟨α, ?_⟩
    simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using hα
  · -- `Ψ ∘ j ≡ j ∘ φ (mod I)`
    intro α
    have h : aeval (verMon r t) (F₀ α + ∑ G ∈ S, C (ω α G) * G) -
        aeval f (verMon (k := k) r t α) = ∑ G ∈ S, C (ω α G) * aeval (verMon r t) G := by
      rw [map_add, (hF₀ α).2, add_sub_cancel_left, map_sum]
      refine Finset.sum_congr rfl fun G _ => ?_
      rw [map_mul, aeval_C, algebraMap_eq]
    rw [h]
    exact Ideal.sum_mem _ fun G hG => Ideal.mul_mem_left _ _ (hS G hG).2

/-! ### Theorem 3.1: the case of a finite field -/

set_option maxHeartbeats 1600000 in
/-- Theorem 3.1 over a finite field: the core is applied over `Ω = k̄`, and the resulting system is
descended to `k` through the finite separable extension `K₀` generated by its coefficients
(Lemma 3.4). -/
theorem theorem_3_1_of_finite [Finite k] (I : Ideal (MvPolynomial (Fin (r + 1)) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (r + 1)) k))
    (t : ℕ) (ht : 1 ≤ t)
    (hgen : ∀ v : Fin (r + 1) → AlgebraicClosure k, v ≠ 0 →
      v ∉ projZeros (AlgebraicClosure k) I →
      ∃ g ∈ I, ∃ e ≤ t, g.IsHomogeneous e ∧ aeval v g ≠ 0)
    (hX : (projZeros (AlgebraicClosure k) I).Nonempty)
    (d : ℕ) (hd : 2 ≤ d) (f : Fin (r + 1) → MvPolynomial (Fin (r + 1)) k)
    (hf : ∀ i, (f i).IsHomogeneous d)
    (hbase : ∀ v ∈ projZeros (AlgebraicClosure k) I, ∃ i, aeval v (f i) ≠ 0) :
    ∃ (ν : Type) (_ : Fintype ν) (s : ℕ) (j : ν → MvPolynomial (Fin (r + 1)) k)
      (Ψ : ν → MvPolynomial ν k),
      1 ≤ s ∧
      (∀ m, (j m).IsHomogeneous s) ∧
      (∀ v ∈ projZeros (AlgebraicClosure k) I, ∃ m, aeval v (j m) ≠ 0) ∧
      (∀ (n : ℕ) (g : MvPolynomial (Fin (r + 1)) k), g.IsHomogeneous (n * s) →
        ∃ G : MvPolynomial ν k, G.IsHomogeneous n ∧ aeval j G = g) ∧
      (∀ m, (Ψ m).IsHomogeneous d) ∧
      (∀ w : ν → AlgebraicClosure k, w ≠ 0 → ∃ m, aeval w (Ψ m) ≠ 0) ∧
      (∀ m, aeval j (Ψ m) - aeval f (j m) ∈ I) := by
  classical
  -- the core over `Ω = k̄`
  obtain ⟨F₀, S, ω, hF₀, hS, hbpf⟩ :=
    exists_extension_core' (κ := AlgebraicClosure k) (Ω := AlgebraicClosure k) I hI t ht hgen hX
      d hd f hf hbase
  -- the field `K₀ = k(ω α G)` of coefficients: a finite separable extension of `k`
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : IntermediateField k (AlgebraicClosure k),
      K₀ = IntermediateField.adjoin k
        (Set.range fun p : VerIdx r t × S => ω p.1 p.2.1) := ⟨_, rfl⟩
  haveI hfin : FiniteDimensional k K₀ := by
    rw [hK₀]
    exact IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral
  haveI hsep : Algebra.IsSeparable k K₀ := inferInstance
  have hmem : ∀ α G, G ∈ S → ω α G ∈ K₀ := by
    intro α G hG
    rw [hK₀]
    exact IntermediateField.subset_adjoin _ _ ⟨(α, ⟨G, hG⟩), rfl⟩
  obtain ⟨ω', hω'⟩ : ∃ ω' : VerIdx r t → MvPolynomial (VerIdx r t) k → K₀,
      ∀ α G, G ∈ S → algebraMap K₀ (AlgebraicClosure k) (ω' α G) = ω α G :=
    ⟨fun α G => if hG : G ∈ S then ⟨ω α G, hmem α G hG⟩ else 0, fun α G hG => by
      dsimp only
      rw [dif_pos hG]
      rfl⟩
  -- the forms over `K₀`
  obtain ⟨F', hF'⟩ : ∃ F' : VerIdx r t → MvPolynomial (VerIdx r t) K₀, ∀ α,
      F' α = MvPolynomial.map (algebraMap k K₀) (F₀ α) +
        ∑ G ∈ S, C (ω' α G) * MvPolynomial.map (algebraMap k K₀) G := ⟨_, fun _ => rfl⟩
  have hF'map : ∀ α, MvPolynomial.map (algebraMap K₀ (AlgebraicClosure k)) (F' α) =
      MvPolynomial.map (algebraMap k (AlgebraicClosure k)) (F₀ α) +
        ∑ G ∈ S, C (ω α G) * MvPolynomial.map (algebraMap k (AlgebraicClosure k)) G := by
    intro α
    rw [hF', map_add, map_sum, map_map, ← IsScalarTower.algebraMap_eq k K₀ (AlgebraicClosure k)]
    congr 1
    refine Finset.sum_congr rfl fun G hG => ?_
    rw [map_mul, map_C, hω' α G hG, map_map,
      ← IsScalarTower.algebraMap_eq k K₀ (AlgebraicClosure k)]
  have hF'hom : ∀ α, (F' α).IsHomogeneous d := by
    intro α
    rw [hF']
    exact ((hF₀ α).1.map _).add
      (IsHomogeneous.sum _ _ _ fun G hG => ((hS G hG).1.map _).C_mul _)
  -- transport to `Fin N`
  obtain ⟨N, ⟨e⟩⟩ : ∃ N : ℕ, Nonempty (VerIdx r t ≃ Fin N) := ⟨_, ⟨Fintype.equivFin _⟩⟩
  obtain ⟨F'', hF''⟩ : ∃ F'' : Fin N → MvPolynomial (Fin N) K₀,
      ∀ n, F'' n = rename e (F' (e.symm n)) := ⟨_, fun _ => rfl⟩
  have hF''hom : ∀ n, (F'' n).IsHomogeneous d := fun n => by
    rw [hF'']
    exact (hF'hom _).rename_isHomogeneous
  have hF''zero : ∀ y : Fin N → AlgebraicClosure k, (∀ n, aeval y (F'' n) = 0) → y = 0 := by
    intro y hy
    by_contra hy0
    have hw : y ∘ e ≠ 0 := by
      intro h0
      apply hy0
      funext m
      have := congrFun h0 (e.symm m)
      simpa using this
    obtain ⟨α, hα⟩ := hbpf (y ∘ e) hw
    apply hα
    rw [← hF'map α, aeval_map_algebraMap]
    have h := hy (e α)
    rwa [hF'', Equiv.symm_apply_apply, aeval_rename] at h
  -- Lemma 3.4: restriction of scalars along a `k`-basis of `K₀`
  obtain ⟨β⟩ : Nonempty (Basis (Fin (Module.finrank k K₀)) k K₀) := ⟨Module.finBasis k K₀⟩
  obtain ⟨G, hG⟩ := exists_restrictScalars β F''
  have hGzero := separable_descent_zero (Ω := AlgebraicClosure k) β F'' hF''zero G hG
  have hGhom := isHomogeneous_restrictScalars β F'' hF''hom G hG
  -- the coordinates of `1 ∈ K₀`
  have hcβ : ∑ a, β.repr 1 a • β a = (1 : K₀) := β.sum_repr 1
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, β.repr 1 a₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h : ∑ a, β.repr 1 a • β a = 0 :=
      Finset.sum_eq_zero fun a _ => by rw [hcon a, zero_smul]
    rw [hcβ] at h
    exact one_ne_zero h
  -- the re-embedding `j`
  obtain ⟨jj, hjj⟩ : ∃ jj : Fin N × Fin (Module.finrank k K₀) → MvPolynomial (Fin (r + 1)) k,
      ∀ m, jj m = C (β.repr 1 m.2) * verMon r t (e.symm m.1) := ⟨_, fun _ => rfl⟩
  refine ⟨Fin N × Fin (Module.finrank k K₀), inferInstance, t, jj, fun m => G m.1 m.2, ht,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `j` is given by forms of degree `t`
    intro m
    rw [hjj]
    exact (verMon_isHomogeneous r t _).C_mul _
  · -- `j` has no base point on `X`
    intro v hv
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv.1
    refine ⟨(e ⟨Finsupp.single i t, Finsupp.degree_single i t⟩, a₀), ?_⟩
    rw [hjj]
    show aeval v (C (β.repr 1 a₀) *
      verMon r t (e.symm (e ⟨Finsupp.single i t, Finsupp.degree_single i t⟩))) ≠ 0
    rw [Equiv.symm_apply_apply, map_mul, aeval_C, aeval_verMon_single]
    exact mul_ne_zero ((map_ne_zero _).2 ha₀) (pow_ne_zero _ hi)
  · -- `j` generates the Veronese subring
    intro n g hg
    obtain ⟨G₀, hG₀hom, hG₀⟩ := exists_rewrite_verMon r t n g (by rwa [mul_comm])
    refine ⟨C ((β.repr 1 a₀)⁻¹ ^ n) * rename (fun α => (e α, a₀)) G₀,
      hG₀hom.rename_isHomogeneous.C_mul _, ?_⟩
    rw [map_mul, aeval_C, algebraMap_eq, aeval_rename]
    have hcomp : (jj ∘ fun α => (e α, a₀)) =
        (C (β.repr 1 a₀) : MvPolynomial (Fin (r + 1)) k) • verMon (k := k) r t := by
      funext α
      simp only [Function.comp_apply, hjj, Equiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcomp, aeval_smul_of_isHomogeneous hG₀hom, hG₀, ← mul_assoc, ← C_pow, ← C_mul, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero n ha₀), C_1, one_mul]
  · -- `Ψ` is homogeneous of degree `d`
    intro m
    exact hGhom m.1 m.2
  · -- `Ψ` has no base point
    intro w hw
    by_contra hcon
    push Not at hcon
    exact hw (hGzero w fun n a => hcon (n, a))
  · -- `Ψ ∘ j ≡ j ∘ φ (mod I)`: compare coefficients along `β`
    rintro ⟨n, a⟩
    show aeval jj (G n a) - aeval f (jj (n, a)) ∈ I
    obtain ⟨α, hα⟩ : ∃ α, α = e.symm n := ⟨_, rfl⟩
    -- the `K₀`-algebra map `Y_m ↦ j_m ⊗ 1` on `k`-rational polynomials
    have hevj_map : ∀ p : MvPolynomial (Fin N × Fin (Module.finrank k K₀)) k,
        aeval (fun m => MvPolynomial.map (algebraMap k K₀) (jj m))
            (MvPolynomial.map (algebraMap k K₀) p) =
          MvPolynomial.map (algebraMap k K₀) (aeval jj p) := by
      intro p
      rw [aeval_map_algebraMap, map_aeval_eq]
    -- ... and on the substituted variables `∑_b β_b Y_{n', b}`
    have hevj_var : ∀ n' : Fin N,
        aeval (fun m => MvPolynomial.map (algebraMap k K₀) (jj m)) (∑ b, C (β b) * X (n', b)) =
          MvPolynomial.map (algebraMap k K₀) (verMon (k := k) r t (e.symm n')) := by
      intro n'
      have h1 := sum_C_mul_map_C_repr_mul β 1 (verMon (k := k) r t (e.symm n'))
      rw [C_1, one_mul] at h1
      rw [map_sum, ← h1]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, aeval_C, aeval_X, algebraMap_eq, hjj]
    -- `ρ_{K₀} (p ⊗ 1) = ρ_k (p) ⊗ 1`
    have hρ' : ∀ p : MvPolynomial (VerIdx r t) k,
        aeval (fun α => MvPolynomial.map (algebraMap k K₀) (verMon (k := k) r t α))
            (MvPolynomial.map (algebraMap k K₀) p) =
          MvPolynomial.map (algebraMap k K₀) (aeval (verMon (k := k) r t) p) := by
      intro p
      rw [aeval_map_algebraMap, map_aeval_eq]
    -- the two sides of the defining identity of `G n`, after substituting `Y_m ↦ j_m`
    have hR : aeval (fun m => MvPolynomial.map (algebraMap k K₀) (jj m))
        (∑ b, C (β b) * MvPolynomial.map (algebraMap k K₀) (G n b)) =
        ∑ b, C (β b) * MvPolynomial.map (algebraMap k K₀) (aeval jj (G n b)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, aeval_C, algebraMap_eq, hevj_map]
    have hL : aeval (fun m => MvPolynomial.map (algebraMap k K₀) (jj m))
        (substBasis (fun a => β a) N (F'' n)) =
        MvPolynomial.map (algebraMap k K₀) (aeval f (verMon (k := k) r t α)) +
          ∑ G ∈ S, C (ω' α G) *
            MvPolynomial.map (algebraMap k K₀) (aeval (verMon (k := k) r t) G) := by
      rw [substBasis, comp_aeval_apply]
      simp only [hevj_var]
      rw [hF'', aeval_rename, ← hα]
      have hc : ((fun n' : Fin N =>
          MvPolynomial.map (algebraMap k K₀) (verMon (k := k) r t (e.symm n'))) ∘ e) =
          fun α => MvPolynomial.map (algebraMap k K₀) (verMon (k := k) r t α) := by
        funext α'
        simp only [Function.comp_apply, Equiv.symm_apply_apply]
      rw [hc, hF', map_add, map_sum, hρ', (hF₀ α).2]
      congr 1
      refine Finset.sum_congr rfl fun G _ => ?_
      rw [map_mul, aeval_C, algebraMap_eq, hρ']
    have hmain := congrArg (aeval (fun m => MvPolynomial.map (algebraMap k K₀) (jj m))) (hG n)
    rw [hL, hR] at hmain
    -- `∑_b β_b · f(j_{n,b}) = f(verMon α)`
    have hf' : ∑ b, C (β b) * MvPolynomial.map (algebraMap k K₀) (aeval f (jj (n, b))) =
        MvPolynomial.map (algebraMap k K₀) (aeval f (verMon (k := k) r t α)) := by
      have h1 : ∀ b, aeval f (jj (n, b)) = C (β.repr 1 b) * aeval f (verMon (k := k) r t α) := by
        intro b
        rw [hjj, map_mul, aeval_C, algebraMap_eq, hα]
      simp only [h1]
      rw [sum_C_mul_map_C_repr_mul β 1, C_1, one_mul]
    -- coefficient comparison
    have hkey : (fun b => aeval jj (G n b) - aeval f (jj (n, b))) =
        fun b => ∑ G ∈ S, C (β.repr (ω' α G) b) * aeval (verMon (k := k) r t) G := by
      apply eq_of_sum_C_mul_map_eq β
      have e1 : ∑ b, C (β b) * MvPolynomial.map (algebraMap k K₀)
          (aeval jj (G n b) - aeval f (jj (n, b))) =
          ∑ b, C (β b) * MvPolynomial.map (algebraMap k K₀) (aeval jj (G n b)) -
            ∑ b, C (β b) * MvPolynomial.map (algebraMap k K₀) (aeval f (jj (n, b))) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_sub, mul_sub]
      rw [e1, ← hmain, hf', add_sub_cancel_left]
      simp only [map_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun G _ => ?_
      exact (sum_C_mul_map_C_repr_mul β (ω' α G) _).symm
    have hfin := congrFun hkey a
    simp only at hfin
    rw [hfin]
    exact Ideal.sum_mem _ fun G hG => Ideal.mul_mem_left _ _ (hS G hG).2

/-! ### Theorem 3.1 -/

/-- **Theorem 3.1 (concrete form).** `X = V(I) ⊆ ℙ^r_k` (`I` homogeneous, `X ≠ ∅`), `L = O_X(1)`,
and `φ : X → X` given by forms `f₀,…,f_r` of degree `d ≥ 2` without common zero on `X`.  Then
there is a re-embedding `j : X ↪ ℙ(ν)` by forms of degree `s` (with `j^*O(1) = L^{⊗s}`, `j`
base-point-free on `X` and generating the Veronese subring) and an endomorphism `Ψ` of `ℙ(ν)` of
degree `d` without base points with `Ψ ∘ j = j ∘ φ` on `X`. -/
theorem theorem_3_1 (I : Ideal (MvPolynomial (Fin (r + 1)) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (r + 1)) k))
    (hX : (projZeros (AlgebraicClosure k) I).Nonempty)
    (d : ℕ) (hd : 2 ≤ d) (f : Fin (r + 1) → MvPolynomial (Fin (r + 1)) k)
    (hf : ∀ i, (f i).IsHomogeneous d)
    (hbase : ∀ v ∈ projZeros (AlgebraicClosure k) I, ∃ i, aeval v (f i) ≠ 0)
    (_hpres : ∀ g ∈ I, aeval f g ∈ I) :
    ∃ (ν : Type) (_ : Fintype ν) (s : ℕ) (j : ν → MvPolynomial (Fin (r + 1)) k)
      (Ψ : ν → MvPolynomial ν k),
      1 ≤ s ∧
      (∀ m, (j m).IsHomogeneous s) ∧
      (∀ v ∈ projZeros (AlgebraicClosure k) I, ∃ m, aeval v (j m) ≠ 0) ∧
      (∀ (n : ℕ) (g : MvPolynomial (Fin (r + 1)) k), g.IsHomogeneous (n * s) →
        ∃ G : MvPolynomial ν k, G.IsHomogeneous n ∧ aeval j G = g) ∧
      (∀ m, (Ψ m).IsHomogeneous d) ∧
      (∀ w : ν → AlgebraicClosure k, w ≠ 0 → ∃ m, aeval w (Ψ m) ≠ 0) ∧
      (∀ m, aeval j (Ψ m) - aeval f (j m) ∈ I) := by
  classical
  -- the degree bound `t`
  obtain ⟨T, hT⟩ : I.FG := IsNoetherian.noetherian I
  have hT' : Ideal.span (T : Set (MvPolynomial (Fin (r + 1)) k)) = I := hT
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = max 1 (T.sup fun g => g.totalDegree) := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by rw [ht]; exact le_max_left _ _
  have htT : ∀ g ∈ T, g.totalDegree ≤ t := by
    intro g hg
    rw [ht]
    exact (Finset.le_sup (f := fun g => g.totalDegree) hg).trans (le_max_right _ _)
  have hgen := hgen_of_span (Ω := AlgebraicClosure k) I hI T hT' t htT
  rcases finite_or_infinite k with hk | hk
  · exact theorem_3_1_of_finite I hI t ht1 hgen hX d hd f hf hbase
  · exact theorem_3_1_of_infinite I hI t ht1 hgen hX d hd f hf hbase

end ArithDyn.Extension
