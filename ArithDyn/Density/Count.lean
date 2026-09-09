import ArithDyn.Density.Map
import ArithDyn.Density.MeanOrder

/-!
# Counting the totally defined points over a finite field (paper §4.2, Proposition 4.5)

For a finite field `K` with `q` elements,
`#ℙ²(K)_f + (𝓐(q-1) + 3) = q² + q + 1`, i.e. `#ℙ²(K)_f = q² + q - 2 - 𝓐(q-1)` (4.6).
-/

set_option autoImplicit false

namespace ArithDyn.Density

open Projectivization Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The bad chart parameters: `v ≠ 1` and `uⁿ v = 1` for some `n` (cf. (4.14)). -/
def S₁ (K : Type*) [Field K] : Set (K × K) := {p | p.2 ≠ 1 ∧ ∃ n : ℕ, p.1 ^ n * p.2 = 1}

lemma S₁_fst_ne_zero {p : K × K} (hp : p ∈ S₁ K) : p.1 ≠ 0 := by
  intro h0
  obtain ⟨hv, n, hn⟩ := hp
  rw [h0] at hn
  cases n with
  | zero => simp at hn; exact hv hn
  | succ n => simp at hn

lemma S₁_snd_ne_zero {p : K × K} (hp : p ∈ S₁ K) : p.2 ≠ 0 := by
  intro h0
  obtain ⟨_, n, hn⟩ := hp
  rw [h0, mul_zero] at hn
  exact zero_ne_one hn

/-- The fibre over a unit `u`: the elements of `⟨u⟩ \ {1}`. -/
abbrev W (u : Kˣ) := {w : Kˣ // w ∈ Subgroup.zpowers u ∧ w ≠ 1}

/-- `S₁ ≃ Σ_u (⟨u⟩ \ {1})`. -/
noncomputable def S₁Equiv : S₁ K ≃ Σ u : Kˣ, W u where
  toFun p := ⟨Units.mk0 p.1.1 (S₁_fst_ne_zero p.2), ⟨Units.mk0 p.1.2 (S₁_snd_ne_zero p.2), by
      obtain ⟨hv, n, hn⟩ := p.2
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_zpowers_iff]
        refine ⟨-(n : ℤ), ?_⟩
        ext
        rw [zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
          Units.val_mk0, Units.val_mk0]
        exact (eq_inv_of_mul_eq_one_right hn).symm
      · intro h
        apply hv
        simpa using congrArg Units.val h⟩⟩
  invFun x := ⟨((x.1 : K), (x.2.1 : K)), by
      obtain ⟨u, w, hw, hw1⟩ := x
      refine ⟨fun h => hw1 (Units.val_eq_one.1 h), ?_⟩
      have hmem : w⁻¹ ∈ Subgroup.zpowers u := Subgroup.inv_mem _ hw
      rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
      obtain ⟨n, hn⟩ := hmem
      refine ⟨n, ?_⟩
      have := congrArg Units.val (congrArg (· * w) hn)
      simpa using this⟩
  left_inv p := by ext <;> simp
  right_inv x := by
    rcases x with ⟨u, w, hw⟩
    exact Sigma.subtype_ext (by simp) (by simp)

lemma card_W (u : Kˣ) : Nat.card (W u) = orderOf u - 1 := by
  have e : W u ≃ ↥((Subgroup.zpowers u : Set Kˣ) \ {1}) :=
    Equiv.subtypeEquivRight (fun w => by simp [Set.mem_diff])
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_diff_singleton_of_mem (Subgroup.one_mem _)]
  congr 1
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_zpowers u

lemma card_S₁ : Nat.card (S₁ K) = ∑ u : Kˣ, (orderOf u - 1) := by
  rw [Nat.card_congr S₁Equiv, Nat.card_sigma]
  simp only [card_W]

lemma sum_orderOf_sub_one :
    ∑ u : Kˣ, (orderOf u - 1) + (Fintype.card K - 1) = A (Fintype.card K - 1) := by
  have h1 : ∀ u : Kˣ, orderOf u - 1 + 1 = orderOf u := fun u => Nat.sub_add_cancel (orderOf_pos u)
  rw [← Fintype.card_units, ← sum_orderOf_eq_A Kˣ, ← Finset.card_univ, Finset.card_eq_sum_ones,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun u _ => h1 u)

/-! ### The bad locus -/

/-- The set of points without a totally defined orbit. -/
def bad (K : Type*) [Field K] : Set (P2 K) := {P | ¬ TotallyDefined P}

lemma E_ne_F : (E : P2 K) ≠ F := inf_ne_F 0

lemma Phi_eq_aff (u v : K) : Phi u v = aff (v - 1) (u * (v - 1)) := rfl

lemma bad_eq : bad K =
    (fun p : K × K => Phi p.1 p.2) '' S₁ K ∪ (fun b : K => aff 0 b) '' Set.univ ∪ {E, F} := by
  ext P
  simp only [bad, Set.mem_setOf_eq, Set.mem_union, Set.mem_image, Set.mem_univ, true_and,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hP
    rcases exists_normal_form P with ⟨a, b, rfl⟩ | ⟨a, rfl⟩ | rfl
    · by_cases ha : a = 0
      · subst ha; left; right; exact ⟨b, rfl⟩
      · left; left
        refine ⟨(b / a, a + 1), ⟨?_, ?_⟩, (aff_eq_Phi ha b).symm⟩
        · intro h; apply ha; linear_combination h
        · by_contra hcon
          push_neg at hcon
          exact hP ((totallyDefined_aff_iff ha b).2 hcon)
    · by_cases ha : a = 0
      · subst ha; right; left; rfl
      · exact absurd (totallyDefined_inf ha) hP
    · right; right; rfl
  · rintro ((⟨⟨u, v⟩, ⟨hv, n, hn⟩, rfl⟩ | ⟨b, rfl⟩) | rfl | rfl)
    · intro hT; exact ((totallyDefined_Phi_iff hv).1 hT n) hn
    · exact not_totallyDefined_aff_zero b
    · exact not_totallyDefined_E
    · exact not_totallyDefined_F

lemma injOn_Phi : Set.InjOn (fun p : K × K => Phi p.1 p.2) (S₁ K) := by
  rintro ⟨u, v⟩ ⟨hv, -⟩ ⟨u', v'⟩ ⟨hv', -⟩ h
  simp only [Phi_eq_aff, aff_eq_aff_iff] at h
  obtain ⟨h0, h1⟩ := h
  have hvv : v = v' := by linear_combination h0
  subst hvv
  have huu : u = u' := mul_right_cancel₀ (sub_ne_zero.2 hv) h1
  rw [huu]

lemma aff_zero_injective : Function.Injective (fun b : K => aff 0 b) := by
  intro b b' h
  exact (aff_eq_aff_iff.1 h).2

lemma disjoint₁ : Disjoint ((fun p : K × K => Phi p.1 p.2) '' S₁ K) ((fun b : K => aff 0 b) '' Set.univ) := by
  rw [Set.disjoint_left]
  rintro P ⟨⟨u, v⟩, ⟨hv, -⟩, rfl⟩ ⟨b, -, hb⟩
  simp only [Phi_eq_aff, aff_eq_aff_iff] at hb
  exact hv (by linear_combination -hb.1)

lemma disjoint₂ : Disjoint ((fun p : K × K => Phi p.1 p.2) '' S₁ K ∪ (fun b : K => aff 0 b) '' Set.univ)
    ({E, F} : Set (P2 K)) := by
  rw [Set.disjoint_left]
  rintro P (⟨⟨u, v⟩, -, rfl⟩ | ⟨b, -, rfl⟩) h <;>
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact aff_ne_inf _ _ 0 h
    · exact aff_ne_F _ _ h

/-- The number of points without a totally defined orbit is `𝓐(q-1) + 3` (Proposition 4.5). -/
theorem ncard_bad : (bad K).ncard = A (Fintype.card K - 1) + 3 := by
  rw [bad_eq, Set.ncard_union_eq disjoint₂ (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq disjoint₁ (Set.toFinite _) (Set.toFinite _), Set.ncard_pair E_ne_F,
    injOn_Phi.ncard_image, Set.ncard_image_of_injective _ aff_zero_injective, Set.ncard_univ,
    Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq, card_S₁]
  have := sum_orderOf_sub_one (K := K)
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  omega

/-- Proposition 4.5 / (4.6): `#ℙ²(K)_f + (𝓐(q-1) + 3) = #ℙ²(K) = q² + q + 1`. -/
theorem card_totallyDefined_add :
    Nat.card {P : P2 K // TotallyDefined P} + (A (Fintype.card K - 1) + 3) = Nat.card (P2 K) := by
  rw [← ncard_bad]
  have h := Set.ncard_add_ncard_compl {P : P2 K | TotallyDefined P}
  have e : Nat.card {P : P2 K // TotallyDefined P} = ({P : P2 K | TotallyDefined P}).ncard :=
    Nat.card_coe_set_eq _
  rw [e]
  convert h using 3

lemma card_P2 : Nat.card (P2 K) = Fintype.card K ^ 2 + Fintype.card K + 1 := by
  rw [Projectivization.card_of_finrank K (Fin 3 → K) (Module.finrank_fin_fun K),
    Nat.card_eq_fintype_card]
  simp [Finset.sum_range_succ]
  ring

/-- (4.6) in the additive form. -/
theorem card_totallyDefined :
    Nat.card {P : P2 K // TotallyDefined P} + (A (Fintype.card K - 1) + 3) =
      Fintype.card K ^ 2 + Fintype.card K + 1 := by
  rw [card_totallyDefined_add, card_P2]

/-- (4.6): `#ℙ²(𝔽_q)_f = q² + q - 2 - 𝓐(q-1)`. -/
theorem card_totallyDefined' :
    Nat.card {P : P2 K // TotallyDefined P} =
      Fintype.card K ^ 2 + Fintype.card K - 2 - A (Fintype.card K - 1) := by
  have h := card_totallyDefined (K := K)
  generalize Fintype.card K ^ 2 = s at h ⊢
  omega

end ArithDyn.Density
