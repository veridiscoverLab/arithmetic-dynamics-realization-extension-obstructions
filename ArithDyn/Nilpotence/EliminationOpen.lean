import ArithDyn.Nilpotence.Elimination

/-!
# The elimination tool for locally closed sets (paper §5.4, Lemma 5.9 for `Y = V(F) ∩ D(g)`)

Same strategy as `exists_vanishing_poly`, with an extra UFD step in `L[z]`
(`L = Frac K[v,u]`): after stripping `z`-powers from the generator, `G₀ = z^e G₁`, either some
irreducible factor `P` of `G₁` does not divide `g̃` (then `P` and `g̃` are coprime, and a
specialised nonzero root of `P` gives a point of `V(F) ∩ D(g) ∩ U` over the escaping set `E`),
or every irreducible factor divides `g̃`, whence `G₁ ∣ g̃^N` and a nonzero constant multiple of
`z^e g̃^N` lies in the ideal, which yields the vanishing polynomial `d`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ArithDyn.Nilpotence

open MvPolynomial Polynomial

variable {K : Type*} [Field K]

/-- UFD fact: if every normalised factor of `a ≠ 0` divides `b`, then `a ∣ b^N`. -/
lemma dvd_pow_of_forall_normalizedFactors_dvd {R : Type*} [CommMonoidWithZero R]
    [NormalizationMonoid R] [UniqueFactorizationMonoid R] {a b : R} (ha : a ≠ 0)
    (h : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors a, P ∣ b) :
    a ∣ b ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors a) := by
  have h1 : (UniqueFactorizationMonoid.normalizedFactors a).prod ∣
      b ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors a) := by
    have := Multiset.prod_dvd_prod_of_dvd (S := UniqueFactorizationMonoid.normalizedFactors a)
      (fun x => x) (fun _ => b) (fun P hP => h P hP)
    simpa [Multiset.map_id', Multiset.map_const', Multiset.prod_replicate] using this
  exact (UniqueFactorizationMonoid.prod_normalizedFactors ha).dvd_iff_dvd_left.1 h1

lemma φL_X : φL (K := K) Polynomial.X = Polynomial.X := by
  simp [φL]

/-- `sub3` does not kill nonzero polynomials (over an infinite field). -/
lemma sub3_ne_zero [Infinite K] {g : MvPolynomial (Fin 3) K} (hg : g ≠ 0) : sub3 g ≠ 0 := by
  intro h
  apply hg
  have hzero : ∀ a : Fin 3 → K, MvPolynomial.eval a (g * X 2) = 0 := by
    intro a
    rw [map_mul, MvPolynomial.eval_X]
    by_cases hz : a 2 = 0
    · rw [hz, mul_zero]
    · have := specialize_sub3 (a 0 / a 2) (a 1 / a 2) (a 2) g
      rw [h, map_zero, ← eq_scaled_of_ne_zero a hz] at this
      rw [← this, zero_mul]
  have : g * X 2 = 0 := MvPolynomial.funext (fun a => by rw [hzero a, map_zero])
  exact (mul_eq_zero.1 this).resolve_right (MvPolynomial.X_ne_zero 2)

lemma exists_nonroot [Infinite K] {q : Polynomial K} (hq : q ≠ 0) :
    ∃ z : K, z ≠ 0 ∧ q.eval z ≠ 0 := by
  have hfin : Set.Finite ({0} ∪ {z : K | q.IsRoot z}) :=
    (Set.finite_singleton 0).union (Polynomial.finite_setOf_isRoot hq)
  obtain ⟨z, hz⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq,
    not_or] at hz
  exact ⟨z, hz.1, hz.2⟩

/-- Clearing denominators in a Bézout identity. -/
lemma exists_coprime_clear {P g : Polynomial (R2 K)} (h : IsCoprime (φL P) (φL g)) :
    ∃ (A B : Polynomial (R2 K)) (d₁ : R2 K), d₁ ≠ 0 ∧ Polynomial.C d₁ = A * P + B * g := by
  obtain ⟨α, β, hαβ⟩ := h
  obtain ⟨A₀, a₁, ha₁, hA₀⟩ := exists_clear α
  obtain ⟨B₀, b₁, hb₁, hB₀⟩ := exists_clear β
  refine ⟨Polynomial.C b₁ * A₀, Polynomial.C a₁ * B₀, a₁ * b₁, mul_ne_zero ha₁ hb₁,
    φL_injective ?_⟩
  simp only [map_add, map_mul, φL_C, hA₀, hB₀, Polynomial.C_mul]
  linear_combination (-(Polynomial.C (algebraMap (R2 K) (L K) a₁) *
    Polynomial.C (algebraMap (R2 K) (L K) b₁))) * hαβ

set_option maxHeartbeats 1600000 in
/-- **The elimination theorem for a principal open piece.** If every point of
`V F ∩ {g ≠ 0}` reaches `O`, then some nonzero `d ∈ K[v,u]` vanishes on `π(V F ∩ {g ≠ 0} ∩ U)`. -/
theorem exists_vanishing_poly_open [IsAlgClosed K]
    (hfin : ∀ u : K, u ≠ 0 → ∃ M : ℕ, 0 < M ∧ u ^ M = 1)
    (F : Set (MvPolynomial (Fin 3) K)) (g : MvPolynomial (Fin 3) K)
    (hnil : ∀ y ∈ V F, MvPolynomial.eval y g ≠ 0 → ∃ n, 1 ≤ n ∧ T^[n] y = 0) :
    ∃ d : R2 K, d ≠ 0 ∧ ∀ y ∈ V F, MvPolynomial.eval y g ≠ 0 → inU y →
      MvPolynomial.eval ![y 1 / y 2, y 0 / y 2] d = 0 := by
  classical
  -- trivial case `g = 0`
  by_cases hg0 : g = 0
  · exact ⟨1, one_ne_zero, fun y _ hy => absurd (by rw [hg0, map_zero]) hy⟩
  obtain ⟨T, hT⟩ : (Ideal.span (sub3 '' F) : Ideal (Polynomial (R2 K))).FG :=
    IsNoetherian.noetherian _
  haveI : IsPrincipalIdealRing (Polynomial (L K)) := EuclideanDomain.to_principal_ideal_domain
  obtain ⟨G, hG⟩ : ∃ G : Polynomial (L K),
      Ideal.map φL (Ideal.span (sub3 '' F)) = Ideal.span {G} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator _).symm⟩
  have hTdvd : ∀ t ∈ T, G ∣ φL t := by
    intro t ht
    have : φL t ∈ Ideal.map φL (Ideal.span (sub3 '' F)) :=
      Ideal.mem_map_of_mem _ (hT ▸ Ideal.subset_span ht)
    rw [hG] at this
    exact Ideal.mem_span_singleton.1 this
  have hIvanish : ∀ σ : Polynomial (R2 K) →+* K, (∀ t ∈ T, σ t = 0) →
      ∀ q ∈ Ideal.span (sub3 '' F), σ q = 0 := by
    intro σ hσ q hq
    have hle : Ideal.span (sub3 '' F) ≤ RingHom.ker σ := by
      rw [← hT, Ideal.span_le]
      intro t ht
      exact RingHom.mem_ker.2 (hσ t ht)
    exact RingHom.mem_ker.1 (hle hq)
  have hspec : ∀ y ∈ V F, inU y → ∀ q ∈ Ideal.span (sub3 '' F),
      specialize (y 0 / y 2) (y 1 / y 2) (y 2) q = 0 := by
    intro y hy hU q hq
    have hz : y 2 ≠ 0 := hU.2.2
    have hsub : sub3 '' F ⊆ ↑(RingHom.ker (specialize (y 0 / y 2) (y 1 / y 2) (y 2))) := by
      rintro _ ⟨f, hf, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, specialize_sub3, ← eq_scaled_of_ne_zero y hz]
      exact hy f hf
    exact RingHom.mem_ker.1 (Ideal.span_le.2 hsub hq)
  -- a specialisation point in `V F ∩ U` with `g ≠ 0` and projection in `E` is impossible
  have hpoint : ∀ (u₀ v₀ z₀ : K), (u₀, v₀) ∈ Eset K → z₀ ≠ 0 → (∀ t ∈ T, specialize u₀ v₀ z₀ t = 0) →
      specialize u₀ v₀ z₀ (sub3 g) ≠ 0 → False := by
    intro u₀ v₀ z₀ hE hz₀ hkill hgne
    have hmem : (![u₀ * z₀, v₀ * z₀, z₀] : Fin 3 → K) ∈ V F := by
      intro f hf
      have h1 : sub3 f ∈ Ideal.span (sub3 '' F) := Ideal.subset_span ⟨f, hf, rfl⟩
      have h2 := hIvanish _ hkill _ h1
      rwa [specialize_sub3] at h2
    rw [specialize_sub3] at hgne
    exact not_reach_zero_of_Eset hE hz₀ (hnil _ hmem hgne)
  set gt : Polynomial (R2 K) := sub3 g with hgt
  have hgt0 : gt ≠ 0 := sub3_ne_zero hg0
  -- Case `G = 0`: every generator is zero, so `V F = 𝔸³`
  by_cases hG0 : G = 0
  · exfalso
    have hT0 : ∀ t ∈ T, t = 0 := by
      intro t ht
      have := hTdvd t ht
      rw [hG0, zero_dvd_iff] at this
      exact φL_injective (by rw [this, map_zero])
    -- some coefficient of `g̃` is a nonzero element of `R2`
    obtain ⟨k, hk⟩ : ∃ k, gt.coeff k ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hgt0 (Polynomial.ext (fun k => by rw [hcon k, Polynomial.coeff_zero]))
    obtain ⟨⟨u₀, v₀⟩, hE, hne⟩ := exists_Eset_eval_ne_zero hfin hk
    have hq : Polynomial.map (MvPolynomial.eval ![v₀, u₀]) gt ≠ 0 := by
      intro h
      have := congrArg (fun q => Polynomial.coeff q k) h
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
      exact hne this
    obtain ⟨z₀, hz₀, hz₀'⟩ := exists_nonroot hq
    exact hpoint u₀ v₀ z₀ hE hz₀ (fun t ht => by rw [hT0 t ht, map_zero]) hz₀'
  -- clear the denominators of `G`
  obtain ⟨G₀, b, hb, hG₀⟩ := exists_clear G
  have hG₀0 : G₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hG₀
    exact mul_ne_zero (by rw [Ne, Polynomial.C_eq_zero]; exact algebraMap_ne_zero hb) hG0 hG₀.symm
  have hunit : IsUnit (Polynomial.C (algebraMap (R2 K) (L K) b)) := by
    rw [Polynomial.isUnit_C]; exact (algebraMap_ne_zero hb).isUnit
  -- strip the power of `z`
  obtain ⟨G₁, hG₁, hXG₁⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd G₀ hG₀0 0
  simp only [map_zero, sub_zero] at hG₁ hXG₁
  set e := Polynomial.rootMultiplicity 0 G₀ with he
  have hc₀ : G₁.coeff 0 ≠ 0 := fun h => hXG₁ (Polynomial.X_dvd_iff.2 h)
  have hG₁0 : G₁ ≠ 0 := fun h => hc₀ (by rw [h, Polynomial.coeff_zero])
  -- the ideal `J` is generated by `X^e * φL G₁`
  have hJ : Ideal.map φL (Ideal.span (sub3 '' F)) = Ideal.span {Polynomial.X ^ e * φL G₁} := by
    rw [hG]
    have h1 : Polynomial.X ^ e * φL G₁ = Polynomial.C (algebraMap (R2 K) (L K) b) * G := by
      rw [← hG₀, hG₁, map_mul, map_pow, φL_X]
    rw [h1, Ideal.span_singleton_mul_left_unit hunit]
  by_cases hdeg : G₁.natDegree = 0
  · -- `G₁ = C c₀`: `C (b' c₀) z^e ∈ I`
    have hG₁C : G₁ = Polynomial.C (G₁.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hmem : φL G₀ ∈ Ideal.map φL (Ideal.span (↑T : Set (Polynomial (R2 K)))) := by
      rw [hT, hG₀, hG]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self G)
    obtain ⟨b', hb', g₀, hg₀mem, hg₀⟩ := exists_mem_span_of_mem_map T hmem
    have hg₀eq : g₀ = Polynomial.C b' * G₀ := φL_injective (by rw [map_mul, φL_C, hg₀])
    refine ⟨b' * G₁.coeff 0, mul_ne_zero hb' hc₀, ?_⟩
    intro y hy _ hU
    have hz : y 2 ≠ 0 := hU.2.2
    have h1 := hspec y hy hU g₀ (by rw [← hT]; exact hg₀mem)
    rw [hg₀eq, hG₁, hG₁C, map_mul, map_mul, specialize_C, specialize_C, map_pow,
      specialize_apply, Polynomial.map_X, Polynomial.eval_X] at h1
    rw [map_mul]
    rcases mul_eq_zero.1 h1 with h | h
    · rw [h, zero_mul]
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h (pow_ne_zero _ hz)
      · rw [h, mul_zero]
  · have hdeg' : 0 < G₁.natDegree := Nat.pos_of_ne_zero hdeg
    have hφG₁ : φL G₁ ≠ 0 := fun h => hG₁0 (φL_injective (by rw [h, map_zero]))
    by_cases hall : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (φL G₁), P ∣ φL gt
    · -- every irreducible factor divides `g̃`: `G₁ ∣ g̃^N`, and `C b'' z^e g̃^N ∈ I`
      set N := Multiset.card (UniqueFactorizationMonoid.normalizedFactors (φL G₁)) with hN
      have hdvd : Polynomial.X ^ e * φL G₁ ∣ φL (Polynomial.X ^ e * gt ^ N) := by
        rw [map_mul, map_pow, map_pow, φL_X]
        exact mul_dvd_mul_left _ (dvd_pow_of_forall_normalizedFactors_dvd hφG₁ hall)
      have hmem : φL (Polynomial.X ^ e * gt ^ N) ∈
          Ideal.map φL (Ideal.span (↑T : Set (Polynomial (R2 K)))) := by
        rw [hT, hJ]
        exact Ideal.mem_span_singleton.2 hdvd
      obtain ⟨b'', hb'', g₁, hg₁mem, hg₁⟩ := exists_mem_span_of_mem_map T hmem
      have hg₁eq : g₁ = Polynomial.C b'' * (Polynomial.X ^ e * gt ^ N) :=
        φL_injective (by rw [map_mul, φL_C, hg₁])
      refine ⟨b'', hb'', ?_⟩
      intro y hy hgy hU
      have hz : y 2 ≠ 0 := hU.2.2
      have h1 := hspec y hy hU g₁ (by rw [← hT]; exact hg₁mem)
      rw [hg₁eq, map_mul, map_mul, specialize_C, map_pow, map_pow, specialize_apply,
        Polynomial.map_X, Polynomial.eval_X, hgt, specialize_sub3, ← eq_scaled_of_ne_zero y hz]
        at h1
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exfalso
        rcases mul_eq_zero.1 h with h | h
        · exact pow_ne_zero _ hz h
        · exact pow_ne_zero _ hgy h
    · -- some irreducible factor `P` of `G₁` is coprime to `g̃`
      exfalso
      push_neg at hall
      obtain ⟨P, hPmem, hPg⟩ := hall
      have hPirr : Irreducible P := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hPmem
      have hPdvd : P ∣ φL G₁ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPmem
      have hcop : IsCoprime P (φL gt) := hPirr.coprime_iff_not_dvd.2 hPg
      -- integer form `P₀` of `P`
      obtain ⟨P₀, β₀, hβ₀, hP₀⟩ := exists_clear P
      have hβunit : IsUnit (Polynomial.C (algebraMap (R2 K) (L K) β₀)) := by
        rw [Polynomial.isUnit_C]; exact (algebraMap_ne_zero hβ₀).isUnit
      have hP₀0 : P₀ ≠ 0 := by
        intro h
        rw [h, map_zero] at hP₀
        exact hPirr.ne_zero ((mul_eq_zero.1 hP₀.symm).resolve_left hβunit.ne_zero)
      have hcop₀ : IsCoprime (φL P₀) (φL gt) := by
        rw [hP₀, isCoprime_mul_unit_left_left hβunit]; exact hcop
      obtain ⟨A, B, d₁, hd₁, hbez⟩ := exists_coprime_clear hcop₀
      -- degree and constant term of `P₀`
      have hdegP : 0 < P₀.natDegree := by
        have h1 : (φL P₀).natDegree = P₀.natDegree := by
          rw [φL, Polynomial.coe_mapRingHom]
          exact Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective (R2 K) (L K)) P₀
        have h2 : (φL P₀).natDegree = P.natDegree := by
          rw [hP₀, Polynomial.natDegree_C_mul (algebraMap_ne_zero hβ₀)]
        rw [← h1, h2]
        exact Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hPirr)
      have hP₀c : P₀.coeff 0 ≠ 0 := by
        intro h
        have hXP : Polynomial.X ∣ φL P₀ := by
          rw [Polynomial.X_dvd_iff, φL, Polynomial.coe_mapRingHom, Polynomial.coeff_map, h, map_zero]
        rw [hP₀] at hXP
        have hXP' : Polynomial.X ∣ P := (hβunit.dvd_mul_left).1 hXP
        have : Polynomial.X ∣ φL G₁ := hXP'.trans hPdvd
        rw [Polynomial.X_dvd_iff, φL, Polynomial.coe_mapRingHom, Polynomial.coeff_map] at this
        exact hc₀ ((map_eq_zero_iff _ (IsFractionRing.injective (R2 K) (L K))).1 this)
      -- generators: `C (bf t) * t = Hf t * P₀`
      have hTP : ∀ t ∈ T, φL P₀ ∣ φL t := by
        intro t ht
        have h1 : G ∣ φL t := hTdvd t ht
        have h2 : φL G₁ ∣ G := by
          have : φL G₁ ∣ Polynomial.C (algebraMap (R2 K) (L K) b) * G := by
            rw [← hG₀, hG₁, map_mul]; exact dvd_mul_left _ _
          exact (hunit.dvd_mul_left).1 this
        have h3 : φL P₀ ∣ P := by rw [hP₀]; exact (hβunit.mul_left_dvd).2 dvd_rfl
        exact h3.trans (hPdvd.trans (h2.trans h1))
      choose! Hf bf hbf hrel using fun t (ht : t ∈ T) => exists_mul_eq_of_dvd (hTP t ht)
      -- a point of `E` avoiding the leading coefficient, constant term, `d₁` and all `bf t`
      have hP0 : P₀.leadingCoeff * P₀.coeff 0 * d₁ * ∏ t ∈ T, bf t ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hP₀0) hP₀c) hd₁)
          (Finset.prod_ne_zero_iff.2 (fun t ht => hbf t ht))
      obtain ⟨⟨u₀, v₀⟩, hE, hne⟩ := exists_Eset_eval_ne_zero hfin hP0
      simp only [map_mul, map_prod, ne_eq, mul_eq_zero, Finset.prod_eq_zero_iff, not_or,
        not_exists, not_and] at hne
      obtain ⟨⟨⟨hlc, hc0⟩, hd₁'⟩, hbt⟩ := hne
      set p₁ : Polynomial K := Polynomial.map (MvPolynomial.eval ![v₀, u₀]) P₀ with hp₁
      have hp₁deg : p₁.natDegree = P₀.natDegree :=
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlc
      have hp₁deg' : p₁.degree ≠ 0 := by
        have : 0 < p₁.natDegree := by rw [hp₁deg]; exact hdegP
        exact (Polynomial.natDegree_pos_iff_degree_pos.1 this).ne'
      obtain ⟨z₀, hz₀⟩ := IsAlgClosed.exists_root p₁ hp₁deg'
      have hz₀0 : z₀ ≠ 0 := by
        rintro rfl
        apply hc0
        have := hz₀
        rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, hp₁, Polynomial.coeff_map]
          at this
        exact this
      have hkill : ∀ t ∈ T, specialize u₀ v₀ z₀ t = 0 := by
        intro t ht
        have h1 := congrArg (specialize u₀ v₀ z₀) (hrel t ht)
        rw [map_mul, map_mul, specialize_C] at h1
        have h2 : specialize u₀ v₀ z₀ P₀ = 0 := by
          rw [specialize_apply, ← hp₁]; exact hz₀
        rw [h2, mul_zero] at h1
        exact (mul_eq_zero.1 h1).resolve_left (hbt t ht)
      have hgne : specialize u₀ v₀ z₀ gt ≠ 0 := by
        intro h
        have h1 := congrArg (specialize u₀ v₀ z₀) hbez
        rw [specialize_C, map_add, map_mul, map_mul, h, mul_zero, add_zero] at h1
        have h2 : specialize u₀ v₀ z₀ P₀ = 0 := by
          rw [specialize_apply, ← hp₁]; exact hz₀
        rw [h2, mul_zero] at h1
        exact hd₁' h1
      exact hpoint u₀ v₀ z₀ hE hz₀0 hkill hgne

/-- The closed case follows with `g = 1`. -/
theorem exists_vanishing_poly' [IsAlgClosed K]
    (hfin : ∀ u : K, u ≠ 0 → ∃ M : ℕ, 0 < M ∧ u ^ M = 1)
    (F : Set (MvPolynomial (Fin 3) K)) (hnil : ∀ y ∈ V F, ∃ n, 1 ≤ n ∧ T^[n] y = 0) :
    ∃ d : R2 K, d ≠ 0 ∧ ∀ y ∈ V F, inU y → MvPolynomial.eval ![y 1 / y 2, y 0 / y 2] d = 0 := by
  obtain ⟨d, hd0, hd⟩ := exists_vanishing_poly_open hfin F 1 (fun y hy _ => hnil y hy)
  exact ⟨d, hd0, fun y hy hU => hd y hy (by simp) hU⟩

/-! ### Locally closed sets `V F \ V G` -/

/-- `V G = V T` for a finite generating set `T` of the ideal spanned by `G`. -/
lemma exists_finset_V_eq (G : Set (MvPolynomial (Fin 3) K)) :
    ∃ T : Finset (MvPolynomial (Fin 3) K), V (↑T : Set (MvPolynomial (Fin 3) K)) = V G := by
  obtain ⟨T, hT⟩ : (Ideal.span G).FG := IsNoetherian.noetherian _
  refine ⟨T, ?_⟩
  have key : ∀ (S : Set (MvPolynomial (Fin 3) K)) (a : Fin 3 → K),
      a ∈ V S ↔ ∀ f ∈ Ideal.span S, MvPolynomial.eval a f = 0 := by
    intro S a
    constructor
    · intro ha f hf
      have hle : Ideal.span S ≤ RingHom.ker (MvPolynomial.eval a) :=
        Ideal.span_le.2 (fun f hf => RingHom.mem_ker.2 (ha f hf))
      exact RingHom.mem_ker.1 (hle hf)
    · intro ha f hf
      exact ha f (Ideal.subset_span hf)
  ext a
  rw [key, key, hT]

/-- **The elimination theorem for locally closed sets.** -/
theorem exists_vanishing_poly_locallyClosed [IsAlgClosed K]
    (hfin : ∀ u : K, u ≠ 0 → ∃ M : ℕ, 0 < M ∧ u ^ M = 1)
    (F G : Set (MvPolynomial (Fin 3) K))
    (hnil : ∀ y ∈ V F \ V G, ∃ n, 1 ≤ n ∧ T^[n] y = 0) :
    ∃ d : R2 K, d ≠ 0 ∧ ∀ y ∈ V F \ V G, inU y →
      MvPolynomial.eval ![y 1 / y 2, y 0 / y 2] d = 0 := by
  classical
  obtain ⟨TG, hTG⟩ := exists_finset_V_eq G
  rw [← hTG] at hnil ⊢
  have hmem : ∀ y, y ∈ V F \ V (↑TG : Set (MvPolynomial (Fin 3) K)) ↔
      y ∈ V F ∧ ∃ g ∈ TG, MvPolynomial.eval y g ≠ 0 := by
    intro y
    constructor
    · rintro ⟨hyF, hyG⟩
      refine ⟨hyF, ?_⟩
      by_contra hcon
      push_neg at hcon
      exact hyG (fun g hg => hcon g hg)
    · rintro ⟨hyF, g, hg, hgy⟩
      exact ⟨hyF, fun hyG => hgy (hyG g hg)⟩
  -- one polynomial per principal open piece
  have hpiece : ∀ g ∈ TG, ∃ d : R2 K, d ≠ 0 ∧ ∀ y ∈ V F, MvPolynomial.eval y g ≠ 0 → inU y →
      MvPolynomial.eval ![y 1 / y 2, y 0 / y 2] d = 0 := by
    intro g hg
    exact exists_vanishing_poly_open hfin F g (fun y hy hgy => hnil y ((hmem y).2 ⟨hy, g, hg, hgy⟩))
  choose! d hd0 hd using hpiece
  refine ⟨∏ g ∈ TG, d g, Finset.prod_ne_zero_iff.2 hd0, ?_⟩
  intro y hy hU
  obtain ⟨hyF, g, hg, hgy⟩ := (hmem y).1 hy
  rw [map_prod]
  exact Finset.prod_eq_zero hg (hd g hg y hyF hgy hU)

end ArithDyn.Nilpotence
