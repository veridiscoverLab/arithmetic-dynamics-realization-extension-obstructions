import Mathlib

/-!
# Veronese monomials: elementary facts

Let `r, t : ℕ`.  The degree-`t` Veronese embedding of `ℙ^r` is indexed by the set
`VerIdx r t` of exponent vectors `α : Fin (r + 1) →₀ ℕ` of total degree `t`, the coordinate
indexed by `α` being the monomial `u^α`.  This file collects the elementary facts about these
monomials that are used to formalize Theorem 3.1 of the paper:

* `verMon`, `verMon_isHomogeneous`, `eval_verMon`, `aeval_verMon`: the monomials and their
  evaluation;
* `exists_rewrite_verMon`: a form of degree `t * d` is a form of degree `d` in the Veronese
  monomials;
* `verMap_quadric`: the quadric relations `Z_α Z_β = Z_γ Z_δ` (`α + β = γ + δ`) hold on Veronese
  points;
* `prod_eq_of_sum_eq`, `exists_verMap_of_quadrics`: a nonzero point satisfying all quadric
  relations is (a scalar multiple of) a Veronese point — the set-theoretic description of the
  Veronese variety.
-/

set_option autoImplicit false

namespace ArithDyn.Extension

open MvPolynomial

/-- Exponent vectors of degree `t` in `r + 1` variables: the index set of the degree-`t` Veronese. -/
abbrev VerIdx (r t : ℕ) : Type := {α : Fin (r + 1) →₀ ℕ // α.degree = t}

namespace VerIdx

variable {r t : ℕ}

theorem ext {α β : VerIdx r t} (h : α.1 = β.1) : α = β := Subtype.ext h

theorem degree_val (α : VerIdx r t) : α.1.degree = t := α.2

theorem sum_val (α : VerIdx r t) : ∑ i, α.1 i = t := by
  rw [← Finsupp.degree_eq_sum]; exact α.2

/-- Two exponent vectors of the same degree, one dominating the other, coincide. -/
theorem eq_of_le {α β : VerIdx r t} (h : β.1 ≤ α.1) : α = β := by
  obtain ⟨δ, hδ⟩ := exists_add_of_le h
  have h2 := congrArg Finsupp.degree hδ
  rw [map_add, α.2, β.2] at h2
  have hδ0 : δ = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
  exact VerIdx.ext (by rw [hδ, hδ0, add_zero])

end VerIdx

theorem setOf_degree_eq_finite (r t : ℕ) : {α : Fin (r + 1) →₀ ℕ | α.degree = t}.Finite :=
  (Finsupp.finite_of_degree_le t).subset (fun _ h => le_of_eq h)

instance instFiniteVerIdx (r t : ℕ) : Finite (VerIdx r t) :=
  (setOf_degree_eq_finite r t).to_subtype

noncomputable instance instFintypeVerIdx (r t : ℕ) : Fintype (VerIdx r t) := Fintype.ofFinite _

instance instDecidableEqVerIdx (r t : ℕ) : DecidableEq (VerIdx r t) :=
  inferInstanceAs (DecidableEq {α : Fin (r + 1) →₀ ℕ // α.degree = t})

instance instNonemptyVerIdx (r t : ℕ) : Nonempty (VerIdx r t) :=
  ⟨⟨Finsupp.single 0 t, Finsupp.degree_single _ _⟩⟩

/-! ### Veronese monomials -/

variable {k : Type*} [CommRing k]

/-- The Veronese monomial `u^α`. -/
noncomputable def verMon (r t : ℕ) (α : VerIdx r t) : MvPolynomial (Fin (r + 1)) k :=
  monomial α.1 1

theorem verMon_isHomogeneous (r t : ℕ) (α : VerIdx r t) :
    (verMon (k := k) r t α).IsHomogeneous t := by
  unfold verMon
  exact isHomogeneous_monomial 1 α.2

theorem eval_verMon {K : Type*} [CommRing K] (r t : ℕ) (α : VerIdx r t) (v : Fin (r + 1) → K) :
    eval v (verMon (k := K) r t α) = ∏ i, v i ^ α.1 i := by
  rw [verMon, eval_monomial, one_mul, Finsupp.prod_fintype]
  exact fun i => pow_zero _

theorem aeval_verMon {K : Type*} [CommRing K] [Algebra k K] (r t : ℕ) (α : VerIdx r t)
    (v : Fin (r + 1) → K) :
    aeval v (verMon (k := k) r t α) = ∏ i, v i ^ α.1 i := by
  rw [verMon, aeval_monomial, map_one, one_mul, Finsupp.prod_fintype]
  exact fun i => pow_zero _

/-! ### Rewriting forms of degree `t * d` in the Veronese monomials -/

/-- Every exponent vector of degree `t * d` is a sum of `d` exponent vectors of degree `t`. -/
theorem exists_sum_val_eq (r t d : ℕ) :
    ∀ γ : Fin (r + 1) →₀ ℕ, γ.degree = t * d → ∃ f : Fin d → VerIdx r t, ∑ j, (f j).1 = γ := by
  induction d with
  | zero =>
    intro γ hγ
    refine ⟨Fin.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    rw [mul_zero] at hγ
    exact ((Finsupp.degree_eq_zero_iff _).1 hγ).symm
  | succ d ih =>
    intro γ hγ
    rw [Nat.mul_succ] at hγ
    obtain ⟨α, hαγ, hα⟩ :=
      Finsupp.exists_le_degree_eq γ t (by rw [hγ]; exact Nat.le_add_left t (t * d))
    have hsub : (γ - α).degree = t * d := by
      have h1 : α + (γ - α) = γ := add_tsub_cancel_of_le hαγ
      have h2 := congrArg Finsupp.degree h1
      rw [map_add, hα, hγ] at h2
      omega
    obtain ⟨f', hf'⟩ := ih (γ - α) hsub
    refine ⟨Fin.cons ⟨α, hα⟩ f', ?_⟩
    rw [Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [hf']
    exact add_tsub_cancel_of_le hαγ

theorem aeval_verMon_prod_X {ι : Type*} (r t : ℕ) (s : Finset ι) (f : ι → VerIdx r t) :
    aeval (verMon (k := k) r t) (∏ j ∈ s, (X (f j) : MvPolynomial (VerIdx r t) k)) =
      monomial (∑ j ∈ s, (f j).1) 1 := by
  rw [map_prod, monomial_sum_one]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [aeval_X]
  rfl

/-- Every form of degree `t * d` is a form of degree `d` in the Veronese monomials. -/
theorem exists_rewrite_verMon (r t d : ℕ) (g : MvPolynomial (Fin (r + 1)) k)
    (hg : g.IsHomogeneous (t * d)) :
    ∃ G : MvPolynomial (VerIdx r t) k, G.IsHomogeneous d ∧ aeval (verMon r t) G = g := by
  choose! f hf using exists_sum_val_eq r t d
  refine ⟨∑ γ ∈ g.support, C (coeff γ g) * ∏ j, X (f γ j), ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ (fun γ _ => ?_)
    have h := (isHomogeneous_C (VerIdx r t) (coeff γ g)).mul
      (IsHomogeneous.prod Finset.univ (fun j => (X (f γ j) : MvPolynomial (VerIdx r t) k))
        (fun _ => 1) (fun j _ => isHomogeneous_X _ _))
    convert h using 1
    simp
  · conv_rhs => rw [g.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun γ hγ => ?_)
    have hγd : γ.degree = t * d := by
      by_contra h
      exact (mem_support_iff.1 hγ) (hg.coeff_eq_zero h)
    rw [map_mul, aeval_C, aeval_verMon_prod_X, hf γ hγd, algebraMap_eq, C_mul_monomial, mul_one]

/-! ### Quadric relations -/

/-- Quadric Veronese relations vanish on Veronese points. -/
theorem verMap_quadric {K : Type*} [CommRing K] (r t : ℕ) (v : Fin (r + 1) → K)
    (α β γ δ : VerIdx r t) (h : α.1 + β.1 = γ.1 + δ.1) :
    (∏ i, v i ^ α.1 i) * (∏ i, v i ^ β.1 i) = (∏ i, v i ^ γ.1 i) * (∏ i, v i ^ δ.1 i) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← pow_add, ← pow_add]
  have hi := DFunLike.congr_fun h i
  rw [Finsupp.add_apply, Finsupp.add_apply] at hi
  rw [hi]

/-! ### Multiset and `Finsupp` bookkeeping -/

theorem multiset_sum_apply {ι : Type*} (s : Multiset (ι →₀ ℕ)) (i : ι) :
    s.sum i = (s.map fun f => f i).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

theorem multiset_map_finsetSum {ι A B : Type*} (s : Finset ι) (f : ι → Multiset A) (g : A → B) :
    (∑ i ∈ s, f i).map g = ∑ i ∈ s, (f i).map g :=
  map_sum (Multiset.mapAddMonoidHom g) f s

theorem sum_nsmul_const {ι M : Type*} [AddCommMonoid M] (s : Finset ι) (f : ι → ℕ) (A : M) :
    ∑ i ∈ s, f i • A = (∑ i ∈ s, f i) • A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_nsmul, ih]

theorem nsmul_single_nat {ι : Type*} [DecidableEq ι] (i : ι) (n m : ℕ) :
    n • Finsupp.single i m = Finsupp.single i (n * m) := by
  ext j
  simp only [Finsupp.coe_nsmul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply]
  split_ifs <;> simp

section Moves

variable {r t : ℕ}

theorem exists_mem_pos_of_sum_pos (s : Multiset (VerIdx r t)) (w : Fin (r + 1))
    (h : 0 < (s.map Subtype.val).sum w) : ∃ α ∈ s, 0 < α.1 w := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt, Nat.le_zero] at hcon
  have h0 : (s.map Subtype.val).sum w = 0 := by
    rw [multiset_sum_apply]
    refine Multiset.sum_eq_zero (fun x hx => ?_)
    rw [Multiset.map_map, Multiset.mem_map] at hx
    obtain ⟨α, hα, rfl⟩ := hx
    exact hcon α hα
  omega

theorem sub_single_add_single_apply (α : Fin (r + 1) →₀ ℕ) (u w i : Fin (r + 1)) :
    (α - Finsupp.single u 1 + Finsupp.single w 1 : Fin (r + 1) →₀ ℕ) i =
      α i - (if u = i then 1 else 0) + (if w = i then 1 else 0) := by
  rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Finsupp.single_apply]

theorem degree_sub_single_add_single {α : Fin (r + 1) →₀ ℕ} {u : Fin (r + 1)} (hu : 1 ≤ α u)
    (w : Fin (r + 1)) :
    (α - Finsupp.single u 1 + Finsupp.single w 1).degree = α.degree := by
  have h1 : Finsupp.single u 1 ≤ α := Finsupp.single_le_iff.2 hu
  have h2 : α - Finsupp.single u 1 + Finsupp.single u 1 = α := tsub_add_cancel_of_le h1
  have h3 := congrArg Finsupp.degree h2
  rw [map_add, Finsupp.degree_single] at h3
  rw [map_add, Finsupp.degree_single]
  omega

/-- One-sided `ℓ¹`-defect of `α` below `β`: `∑ i, (β i - α i)` (truncated subtraction). -/
def defect (α β : Fin (r + 1) →₀ ℕ) : ℕ := ∑ i, (β i - α i)

theorem eq_of_defect_eq_zero {α β : VerIdx r t} (h : defect α.1 β.1 = 0) : α = β := by
  apply VerIdx.eq_of_le
  rw [Finsupp.le_def]
  intro i
  unfold defect at h
  have hi : β.1 i - α.1 i ≤ ∑ j, (β.1 j - α.1 j) :=
    Finset.single_le_sum (f := fun j => β.1 j - α.1 j) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
  omega

theorem defect_move {α α' β : Fin (r + 1) →₀ ℕ} {u w : Fin (r + 1)} (hu : β u < α u)
    (hw : α w < β w)
    (hα' : ∀ i, α' i = α i - (if u = i then 1 else 0) + (if w = i then 1 else 0)) :
    defect α' β + 1 = defect α β := by
  have huw : u ≠ w := by rintro rfl; omega
  unfold defect
  have hrest : ∑ i ∈ Finset.univ.erase w, (β i - α' i) =
      ∑ i ∈ Finset.univ.erase w, (β i - α i) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hiw : w ≠ i := (Finset.ne_of_mem_erase hi).symm
    rw [hα' i, if_neg hiw, add_zero]
    by_cases hiu : u = i
    · subst hiu; rw [if_pos rfl]; omega
    · rw [if_neg hiu, Nat.sub_zero]
  have hw' : α' w = α w + 1 := by rw [hα' w, if_neg huw, if_pos rfl, Nat.sub_zero]
  have h1 : ∑ i, (β i - α' i) = (β w - α' w) + ∑ i ∈ Finset.univ.erase w, (β i - α' i) :=
    (Finset.add_sum_erase Finset.univ (fun i => β i - α' i) (Finset.mem_univ w)).symm
  have h2 : ∑ i, (β i - α i) = (β w - α w) + ∑ i ∈ Finset.univ.erase w, (β i - α i) :=
    (Finset.add_sum_erase Finset.univ (fun i => β i - α i) (Finset.mem_univ w)).symm
  rw [h1, h2, hrest, hw']
  omega

/-- Exchange moves: if `β ≤ α + Σ s`, then the multiset `α ::ₘ s` can be transformed, without
changing the number of elements, the exponent sum, or the product of `P`-values, into a multiset
of the form `β ::ₘ s'`. -/
theorem exists_reach {K : Type*} [CommMonoid K] (P : VerIdx r t → K)
    (hquad : ∀ α β γ δ : VerIdx r t, α.1 + β.1 = γ.1 + δ.1 → P α * P β = P γ * P δ)
    (β : VerIdx r t) (n : ℕ) :
    ∀ (α : VerIdx r t) (s : Multiset (VerIdx r t)), defect α.1 β.1 ≤ n →
      β.1 ≤ α.1 + (s.map Subtype.val).sum →
      ∃ s' : Multiset (VerIdx r t), Multiset.card s' = Multiset.card s ∧
        β.1 + (s'.map Subtype.val).sum = α.1 + (s.map Subtype.val).sum ∧
        P β * (s'.map P).prod = P α * (s.map P).prod := by
  induction n with
  | zero =>
    intro α s hd _
    obtain rfl : α = β := eq_of_defect_eq_zero (Nat.le_zero.1 hd)
    exact ⟨s, rfl, rfl, rfl⟩
  | succ n ih =>
    intro α s hd hle
    by_cases hαβ : α = β
    · subst hαβ; exact ⟨s, rfl, rfl, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, α.1 w < β.1 w := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      exact hαβ (VerIdx.eq_of_le (Finsupp.le_def.2 hcon))
    obtain ⟨u, hu⟩ : ∃ u, β.1 u < α.1 u := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      exact hαβ (VerIdx.eq_of_le (Finsupp.le_def.2 hcon)).symm
    have hpos : 0 < (s.map Subtype.val).sum w := by
      have := Finsupp.le_def.1 hle w
      rw [Finsupp.add_apply] at this
      omega
    obtain ⟨α', hα's, hα'w⟩ := exists_mem_pos_of_sum_pos s w hpos
    obtain ⟨s₂, rfl⟩ := Multiset.exists_cons_of_mem hα's
    have hu1 : 1 ≤ α.1 u := by omega
    have hw1 : 1 ≤ α'.1 w := hα'w
    obtain ⟨αn, hαn⟩ : ∃ αn : VerIdx r t, αn.1 = α.1 - Finsupp.single u 1 + Finsupp.single w 1 :=
      ⟨⟨_, by rw [degree_sub_single_add_single hu1 w, α.2]⟩, rfl⟩
    obtain ⟨α'n, hα'n⟩ :
        ∃ α'n : VerIdx r t, α'n.1 = α'.1 - Finsupp.single w 1 + Finsupp.single u 1 :=
      ⟨⟨_, by rw [degree_sub_single_add_single hw1 u, α'.2]⟩, rfl⟩
    have hkey : αn.1 + α'n.1 = α.1 + α'.1 := by
      ext i
      rw [Finsupp.add_apply, Finsupp.add_apply, hαn, hα'n, sub_single_add_single_apply,
        sub_single_add_single_apply]
      split_ifs <;> subst_vars <;> omega
    have hdn : defect αn.1 β.1 ≤ n := by
      have := defect_move (α' := αn.1) hu hw (fun i => by rw [hαn, sub_single_add_single_apply])
      omega
    have hsum_s : ((α' ::ₘ s₂).map Subtype.val).sum = α'.1 + (s₂.map Subtype.val).sum := by
      rw [Multiset.map_cons, Multiset.sum_cons]
    have hsum_n : ((α'n ::ₘ s₂).map Subtype.val).sum = α'n.1 + (s₂.map Subtype.val).sum := by
      rw [Multiset.map_cons, Multiset.sum_cons]
    have htot : αn.1 + ((α'n ::ₘ s₂).map Subtype.val).sum =
        α.1 + ((α' ::ₘ s₂).map Subtype.val).sum := by
      rw [hsum_s, hsum_n, ← add_assoc, ← add_assoc, hkey]
    obtain ⟨s', hc, hs, hp⟩ := ih αn (α'n ::ₘ s₂) hdn (by rw [htot]; exact hle)
    refine ⟨s', ?_, ?_, ?_⟩
    · rw [hc, Multiset.card_cons, Multiset.card_cons]
    · rw [hs, htot]
    · rw [hp, Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
        ← mul_assoc, ← mul_assoc, hquad αn α'n α α' hkey]

end Moves

/-- Products of `P`-values over a multiset of exponents depend only on the number of factors and
the sum of the exponents, when `P` satisfies all quadric relations. -/
theorem prod_eq_of_sum_eq {K : Type*} [Field K] (r t : ℕ) (P : VerIdx r t → K)
    (hquad : ∀ α β γ δ : VerIdx r t, α.1 + β.1 = γ.1 + δ.1 → P α * P β = P γ * P δ)
    (s s' : Multiset (VerIdx r t)) (hcard : Multiset.card s = Multiset.card s')
    (hsum : (s.map Subtype.val).sum = (s'.map Subtype.val).sum) :
    (s.map P).prod = (s'.map P).prod := by
  obtain ⟨n, hn⟩ : ∃ n, Multiset.card s = n := ⟨_, rfl⟩
  induction n generalizing s s' with
  | zero =>
    obtain rfl : s = 0 := Multiset.card_eq_zero.1 hn
    obtain rfl : s' = 0 := Multiset.card_eq_zero.1 (by omega)
    rfl
  | succ n ih =>
    obtain ⟨α, hα⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card s)
    obtain ⟨s₁, rfl⟩ := Multiset.exists_cons_of_mem hα
    obtain ⟨β, hβ⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card s')
    obtain ⟨s₁', rfl⟩ := Multiset.exists_cons_of_mem hβ
    rw [Multiset.card_cons] at hn hcard
    rw [Multiset.card_cons] at hcard
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons] at hsum
    have hle : β.1 ≤ α.1 + (s₁.map Subtype.val).sum := by rw [hsum]; exact le_self_add
    obtain ⟨s₁'', hc, hs, hp⟩ := exists_reach P hquad β _ α s₁ le_rfl hle
    have hrec := ih s₁'' s₁' (by omega) (by rw [hsum] at hs; exact add_left_cancel hs) (by omega)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, ← hp, hrec]

/-- **Set-theoretic Veronese**: a nonzero point satisfying all quadric relations is (a scalar
multiple of) a Veronese point. -/
theorem exists_verMap_of_quadrics {K : Type*} [Field K] (r t : ℕ) (ht : 1 ≤ t)
    (P : VerIdx r t → K) (hP : P ≠ 0)
    (hquad : ∀ α β γ δ : VerIdx r t, α.1 + β.1 = γ.1 + δ.1 → P α * P β = P γ * P δ) :
    ∃ (v : Fin (r + 1) → K) (c : K), v ≠ 0 ∧ c ≠ 0 ∧ ∀ α, P α = c * ∏ i, v i ^ α.1 i := by
  obtain ⟨α₀, hα₀⟩ : ∃ α₀, P α₀ ≠ 0 := Function.ne_iff.1 hP
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, 1 ≤ α₀.1 i₀ := by
    by_contra hcon
    simp only [not_exists, not_le] at hcon
    have h0 : α₀.1 = 0 := Finsupp.ext (fun i => by
      have := hcon i
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega)
    have := α₀.2
    rw [h0, map_zero] at this
    omega
  have hμdeg : ∀ i, (α₀.1 - Finsupp.single i₀ 1 + Finsupp.single i 1).degree = t := fun i => by
    rw [degree_sub_single_add_single hi₀ i, α₀.2]
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin (r + 1) → VerIdx r t,
      ∀ i, (μ i).1 = α₀.1 - Finsupp.single i₀ 1 + Finsupp.single i 1 :=
    ⟨fun i => ⟨_, hμdeg i⟩, fun i => rfl⟩
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : VerIdx r t, σ₀.1 = Finsupp.single i₀ t :=
    ⟨⟨_, Finsupp.degree_single _ _⟩, rfl⟩
  have hμi₀ : μ i₀ = α₀ := by
    apply VerIdx.ext
    rw [hμ i₀]
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hi₀)
  have e1 : Finsupp.single i₀ 1 ≤ α₀.1 := Finsupp.single_le_iff.2 hi₀
  -- the main identity, from `prod_eq_of_sum_eq`
  have claim : ∀ α : VerIdx r t, P α₀ ^ t * P α = P σ₀ * ∏ i, P (μ i) ^ α.1 i := by
    intro α
    have h := prod_eq_of_sum_eq r t P hquad (α ::ₘ Multiset.replicate t α₀)
      (σ₀ ::ₘ ∑ i, Multiset.replicate (α.1 i) (μ i)) ?_ ?_
    · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_replicate, Multiset.prod_replicate,
        Multiset.map_cons, Multiset.prod_cons, multiset_map_finsetSum, Multiset.prod_sum] at h
      simp only [Multiset.map_replicate, Multiset.prod_replicate] at h
      rw [mul_comm (P α₀ ^ t)]
      exact h
    · rw [Multiset.card_cons, Multiset.card_replicate, Multiset.card_cons, Multiset.card_sum]
      simp only [Multiset.card_replicate]
      rw [VerIdx.sum_val]
    · rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_replicate, Multiset.sum_replicate,
        Multiset.map_cons, Multiset.sum_cons, multiset_map_finsetSum, Multiset.sum_sum]
      simp only [Multiset.map_replicate, Multiset.sum_replicate, hμ, hσ₀]
      calc α.1 + t • α₀.1
          = α.1 + t • (Finsupp.single i₀ 1 + (α₀.1 - Finsupp.single i₀ 1)) := by
            rw [add_tsub_cancel_of_le e1]
        _ = Finsupp.single i₀ t + (t • (α₀.1 - Finsupp.single i₀ 1) + α.1) := by
            rw [nsmul_add, nsmul_single_nat, mul_one]
            abel
        _ = Finsupp.single i₀ t +
              ∑ i, α.1 i • (α₀.1 - Finsupp.single i₀ 1 + Finsupp.single i 1) := by
            congr 1
            simp only [nsmul_add, Finset.sum_add_distrib, sum_nsmul_const, VerIdx.sum_val,
              nsmul_single_nat, mul_one, Finsupp.univ_sum_single]
  have hσ₀ne : P σ₀ ≠ 0 := by
    intro h0
    have h := claim α₀
    rw [h0, zero_mul] at h
    exact mul_ne_zero (pow_ne_zero _ hα₀) hα₀ h
  refine ⟨fun i => P (μ i), P σ₀ / P α₀ ^ t, ?_, div_ne_zero hσ₀ne (pow_ne_zero _ hα₀),
    fun α => ?_⟩
  · intro h
    have := congrFun h i₀
    simp only [Pi.zero_apply, hμi₀] at this
    exact hα₀ this
  · have h := claim α
    show P α = P σ₀ / P α₀ ^ t * ∏ i, P (μ i) ^ α.1 i
    rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ hα₀), mul_comm (P α), h]

end ArithDyn.Extension
