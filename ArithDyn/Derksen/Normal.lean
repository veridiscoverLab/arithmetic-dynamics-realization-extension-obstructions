import ArithDyn.Derksen.ZRec

/-!
# `p`-normal sets and the reduction of Theorem 2.2 to Proposition 2.7 (paper §2.1, §2.5)

We formalise Definition 2.1 (elementary `p`-nested sets, `p`-normal sets), the statements of
Theorem 2.2 and Propositions 2.6/2.7, and prove the last step of the paper's argument:
**Proposition 2.7 implies Theorem 2.2** (`theorem22_of_prop27`). The geometric heart
(Proposition 2.6, via Lemma 2.5 and the projective elimination argument) is *not* formalised.
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

open Finset

/-- `E_q(c) = {∑ᵢ cᵢ q^{kᵢ} : kᵢ ≥ 0} ⊆ ℤ` (Proposition 2.6). -/
def Eset (q : ℕ) {r : ℕ} (c : Fin r → ℤ) : Set ℤ :=
  {n | ∃ k : Fin r → ℕ, n = ∑ i, c i * (q : ℤ) ^ (k i)}

/-- The elementary set `{c₀ + ∑ᵢ cᵢ q^{kᵢ}} ∩ ℕ` (Definition 2.1). -/
def elementarySet (q : ℕ) (c₀ : ℚ) {r : ℕ} (c : Fin r → ℚ) : Set ℕ :=
  {n | ∃ k : Fin r → ℕ, (n : ℚ) = c₀ + ∑ i, c i * (q : ℚ) ^ (k i)}

/-- The data `(q = pᵉ, c₀, c₁, …, c_r)` of an elementary `p`-nested set (Definition 2.1). -/
structure ElementaryData (p : ℕ) where
  e : ℕ
  he : 1 ≤ e
  r : ℕ
  hr : 1 ≤ r
  c₀ : ℚ
  c : Fin r → ℚ
  int_c : ∀ i, ∃ z : ℤ, ((p ^ e : ℕ) - 1 : ℚ) * c i = z
  int_c₀ : ∃ z : ℤ, ((p ^ e : ℕ) - 1 : ℚ) * c₀ = z
  int_sum : ∃ z : ℤ, c₀ + ∑ i, c i = z
  ne_zero : ∀ i, c i ≠ 0
  exists_pos : ∃ i, 0 < c i

/-- The elementary `p`-nested set `S_q(c₀; c)` of Definition 2.1. -/
def ElementaryData.set {p : ℕ} (D : ElementaryData p) : Set ℕ := elementarySet (p ^ D.e) D.c₀ D.c

/-- The sets obtained from elementary `p`-nested sets, finite sets and infinite arithmetic
progressions by finite unions. -/
inductive IsPNormalBase (p : ℕ) : Set ℕ → Prop
  | elementary (D : ElementaryData p) : IsPNormalBase p D.set
  | finite {S : Set ℕ} (h : S.Finite) : IsPNormalBase p S
  | progression (a b : ℕ) (ha : 1 ≤ a) : IsPNormalBase p {n | b ≤ n ∧ n % a = b % a}
  | union {S T : Set ℕ} : IsPNormalBase p S → IsPNormalBase p T → IsPNormalBase p (S ∪ T)

/-- `p`-normal sets (Definition 2.1): finite symmetric-difference modifications of the above. -/
def IsPNormal (p : ℕ) (S : Set ℕ) : Prop := ∃ B, IsPNormalBase p B ∧ (symmDiff S B).Finite

/-- **Statement of Theorem 2.2**: every `p`-normal set is the zero set of a linear recurrence
sequence over `𝔽_p(t)` (a solution of a monic constant-coefficient recurrence valid from `n = 0`). -/
def Theorem22 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ S : Set ℕ, IsPNormal p S →
    ∃ (E : LinearRecurrence (RatFunc (ZMod p))) (u : ℕ → RatFunc (ZMod p)),
      E.IsSolution u ∧ {n | u n = 0} = S

/-- **Statement of Proposition 2.7**: `E_{q₀}(c) ∈ 𝓡_p` for every `q₀ = p^f` and all nonzero
integer weights. -/
def Prop27 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ (r : ℕ) (c : Fin r → ℤ), (∀ i, c i ≠ 0) →
    Eset (p ^ f) c ∈ RClass (RatFunc (ZMod p))

/-- **Statement of Proposition 2.6**: `E_q(c) ∈ 𝓡_p` when `q = pᵉ > 4 ∑|cᵢ|`. -/
def Prop26 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ e : ℕ, 1 ≤ e → ∀ (r : ℕ) (c : Fin r → ℤ), 1 ≤ r → (∀ i, c i ≠ 0) →
    4 * (∑ i, (c i).natAbs) < p ^ e → Eset (p ^ e) c ∈ RClass (RatFunc (ZMod p))

/-! ### From bi-infinite zero sets to the elementary sets -/

/-- Recovering the original parameters (proof of Theorem 2.2 in §2.5): with `D = q - 1`,
`dᵢ = D cᵢ`, `n ∈ S_q(c₀; c) ↔ D n - d₀ ∈ E_q(d)`. -/
lemma mem_elementarySet_iff {q : ℕ} (hq : 2 ≤ q) {r : ℕ} (c₀ : ℚ) (c : Fin r → ℚ) (d₀ : ℤ)
    (d : Fin r → ℤ) (hd₀ : ((q : ℚ) - 1) * c₀ = d₀) (hd : ∀ i, ((q : ℚ) - 1) * c i = d i) (n : ℕ) :
    n ∈ elementarySet q c₀ c ↔ (((q - 1 : ℕ) : ℤ) * n - d₀) ∈ Eset q d := by
  have hD : ((q : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    linarith
  have hcast : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hcast, ← hd₀]
    simp only [← hd]
    rw [hk, mul_add, Finset.mul_sum, add_sub_cancel_left]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hk' : ((q - 1 : ℕ) : ℚ) * n - d₀ = ∑ i, (d i : ℚ) * (q : ℚ) ^ (k i) := by
      have := congrArg (Int.cast : ℤ → ℚ) hk
      push_cast at this
      exact this
    rw [hcast, ← hd₀] at hk'
    simp only [← hd, mul_assoc] at hk'
    rw [← Finset.mul_sum] at hk'
    have : ((q : ℚ) - 1) * (n - (c₀ + ∑ i, c i * (q : ℚ) ^ (k i))) = 0 := by
      linear_combination hk'
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hD
    · linear_combination h

/-! ### The reduction -/

section Reduction

variable {p : ℕ} [hp : Fact p.Prime]

/-- Every set built by `IsPNormalBase` is the zero set of a linear recurrence sequence over
`𝔽_p(t)`, granted Proposition 2.7. -/
theorem exists_isLinRecSeq_of_isPNormalBase (h27 : Prop27 p) {B : Set ℕ} (hB : IsPNormalBase p B) :
    ∃ u : ℕ → RatFunc (ZMod p), IsLinRecSeq u ∧ ∀ n, u n = 0 ↔ n ∈ B := by
  classical
  induction hB with
  | elementary D =>
    -- `q = pᵉ`, `D' = q - 1`, `dᵢ = D' cᵢ`
    have hq : 2 ≤ p ^ D.e :=
      le_trans hp.out.two_le (Nat.le_self_pow (by have := D.he; omega) p)
    choose d hd using D.int_c
    obtain ⟨d₀, hd₀⟩ := D.int_c₀
    have hdne : ∀ i, d i ≠ 0 := by
      intro i h
      have h1 := hd i
      rw [h, Int.cast_zero, mul_eq_zero] at h1
      rcases h1 with h1 | h1
      · have : (2 : ℚ) ≤ (p ^ D.e : ℕ) := by exact_mod_cast hq
        linarith
      · exact D.ne_zero i h1
    have hE := h27 D.e D.he D.r d hdne
    have hE' := RClass.affine_preimage_mem hE ((p ^ D.e - 1 : ℕ) : ℤ) (-d₀)
    obtain ⟨u, hu, hu0⟩ := RClass.exists_isLinRecSeq hE'
    refine ⟨u, hu, fun n => ?_⟩
    rw [hu0 n]
    show ((p ^ D.e - 1 : ℕ) : ℤ) * n + -d₀ ∈ Eset (p ^ D.e) d ↔ n ∈ D.set
    rw [← sub_eq_add_neg, ElementaryData.set,
      mem_elementarySet_iff hq D.c₀ D.c d₀ d (by simpa using hd₀) (fun i => by simpa using hd i) n]
  | finite hS =>
    refine ⟨fun n => if n ∈ hS.toFinset then 0 else 1, ?_, fun n => ?_⟩
    · exact (IsLinRecSeq.const 1).modify hS.toFinset (fun _ => 0)
    · simp [Set.Finite.mem_toFinset]
  | progression a b ha =>
    have hper : IsLinRecSeq (fun n : ℕ => if n % a = b % a then (0 : RatFunc (ZMod p)) else 1) :=
      isLinRecSeq_of_periodic ha (fun n => by simp [Nat.add_mod_right])
    refine ⟨fun n => if n ∈ Finset.range b then 1 else if n % a = b % a then 0 else 1,
      hper.modify (Finset.range b) (fun _ => 1), fun n => ?_⟩
    simp only [Finset.mem_range, Set.mem_setOf_eq]
    by_cases hnb : n < b
    · simp [hnb, not_le.2 hnb]
    · have hbn : b ≤ n := not_lt.1 hnb
      simp [hnb, hbn]
  | union _ _ ihS ihT =>
    obtain ⟨u, hu, hu0⟩ := ihS
    obtain ⟨v, hv, hv0⟩ := ihT
    refine ⟨u * v, hu.mul hv, fun n => ?_⟩
    simp [hu0 n, hv0 n]

/-- **Proposition 2.7 implies Theorem 2.2** (the final step of §2.5 in the paper). -/
theorem theorem22_of_prop27 (h27 : Prop27 p) : Theorem22 p := by
  classical
  intro S ⟨B, hB, hfin⟩
  obtain ⟨u, hu, hu0⟩ := exists_isLinRecSeq_of_isPNormalBase h27 hB
  -- modify `u` on the finite symmetric difference
  set w : ℕ → RatFunc (ZMod p) :=
    fun n => if n ∈ hfin.toFinset then (if n ∈ S then 0 else 1) else u n with hw
  have hwrec : IsLinRecSeq w := hu.modify hfin.toFinset (fun n => if n ∈ S then 0 else 1)
  obtain ⟨E, hE⟩ := exists_isSolution_of_isLinRecSeq hwrec
  refine ⟨E, w, hE, ?_⟩
  ext n
  simp only [Set.mem_setOf_eq, hw, Set.Finite.mem_toFinset]
  by_cases hsd : n ∈ symmDiff S B
  · simp only [hsd, if_true]
    by_cases hS : n ∈ S <;> simp [hS]
  · simp only [hsd, if_false, hu0 n]
    rw [Set.mem_symmDiff] at hsd
    push_neg at hsd
    exact ⟨hsd.2, hsd.1⟩

end Reduction

end ArithDyn.Derksen
