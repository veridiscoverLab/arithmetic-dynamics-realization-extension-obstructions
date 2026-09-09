import ArithDyn.Derksen.Normal
import ArithDyn.Derksen.FundRec

/-!
# Proposition 2.7 from Proposition 2.6: the circle-gap decomposition (paper §2.4)

For `q₀ = p^f` and nonzero integer weights `c₁, …, c_r` we show that `E_{q₀}(c) ∈ 𝓡_p`
follows from the small-weight case (Proposition 2.6) by Lee–Nam's circle-gap decomposition:
writing each exponent as `kᵢ = m ℓᵢ + ρᵢ` (`0 ≤ ρᵢ < m`), a residue vector `ρ` has a cyclic gap of
length `≥ g = m/(r+1)`; taking the first residue `A` after the gap, all residues lie in the window
`[A, A + m - g]`, and `E_{q₀}(c)` splits into finitely many pieces:
* a *high face* `q₀^A · E_Q(cᵢ q₀^{wᵢ})` with `Q = q₀^m` and `wᵢ ≤ m - g` (Proposition 2.6 applies
  since `4 ∑|cᵢ| q₀^{wᵢ} < Q`), and
* *low faces* `cᵢ q₀^{ρᵢ} + E_Q((c_j q₀^{ρ_j})_{j ≠ i})` with one term fewer (induction on `r`).
The gap is found by a pigeonhole walk: if every residue had another residue strictly within
distance `g - 1` before it, walking backwards `r + 1` times would produce `r + 2` distinct
residues among `r + 1`.
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

open Finset

variable {K : Type*} [Field K]

/-! ### Finite unions in `𝓡` -/

theorem RClass.finset_biUnion_mem {ι : Type*} (s : Finset ι) (S : ι → Set ℤ)
    (h : ∀ i ∈ s, S i ∈ RClass K) : (⋃ i ∈ s, S i) ∈ RClass K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RClass.empty_mem (K := K)
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact RClass.union_mem (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem RClass.iUnion_mem {ι : Type*} [Fintype ι] (S : ι → Set ℤ) (h : ∀ i, S i ∈ RClass K) :
    (⋃ i, S i) ∈ RClass K := by
  have := RClass.finset_biUnion_mem (K := K) Finset.univ S (fun i _ => h i)
  simpa using this

/-! ### The cyclic gap lemma -/

/-- Backward cyclic distance from `x` to `y` on a circle of length `m` (for `x, y < m`). -/
def back (m x y : ℕ) : ℕ := if y ≤ x then x - y else x + m - y

lemma back_lt {m x y : ℕ} (hx : x < m) (hy : y < m) : back m x y < m := by
  unfold back; split_ifs <;> omega

lemma back_eq_zero_iff {m x y : ℕ} (hx : x < m) (hy : y < m) : back m x y = 0 ↔ x = y := by
  unfold back; split_ifs <;> omega

lemma back_add_back {m x y : ℕ} (hx : x < m) (hy : y < m) (hxy : x ≠ y) :
    back m x y + back m y x = m := by
  unfold back; split_ifs <;> omega

lemma back_int_cases (m x y : ℕ) (hy : y < m) :
    ((back m x y : ℕ) : ℤ) = x - y ∨ ((back m x y : ℕ) : ℤ) = x - y + m := by
  unfold back; split_ifs with h
  · left; rw [Nat.cast_sub h]
  · right
    have : y ≤ x + m := by omega
    rw [Nat.cast_sub this]; push_cast; ring

/-- **Cyclic gap lemma.** Among `r + 1` residues on a circle of length `m = (r + 1) g`, some
residue `ρ i₀` is preceded by a gap of length `≥ g`: every residue lies within forward distance
`m - g` of `ρ i₀`. -/
theorem exists_gap {m g r : ℕ} (hg : 1 ≤ g) (hm : m = (r + 1) * g) (ρ : Fin (r + 1) → ℕ)
    (hρ : ∀ i, ρ i < m) : ∃ i₀, ∀ i, back m (ρ i) (ρ i₀) ≤ m - g := by
  classical
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  by_contra hcon
  push_neg at hcon
  -- `f i₀` is a residue strictly within distance `g'` before `ρ i₀`
  choose f hf using hcon
  have hd : ∀ i, 1 ≤ back m (ρ i) (ρ (f i)) ∧ back m (ρ i) (ρ (f i)) ≤ g' := by
    intro i
    have h1 := hf i
    have hne : ρ (f i) ≠ ρ i := by
      intro h
      rw [(back_eq_zero_iff (hρ _) (hρ _)).2 h] at h1
      omega
    have h2 := back_add_back (hρ (f i)) (hρ i) hne
    have h3 := back_lt (hρ (f i)) (hρ i)
    constructor <;> omega
  -- the backward walk and the distance travelled
  let w : ℕ → Fin (r + 1) := fun k => f^[k] (0 : Fin (r + 1))
  let D : ℕ → ℕ := fun k => ∑ t ∈ range k, back m (ρ (w t)) (ρ (w (t + 1)))
  have hw : ∀ k, w (k + 1) = f (w k) := fun k => Function.iterate_succ_apply' f k 0
  have hDstep : ∀ k, D (k + 1) = D k + back m (ρ (w k)) (ρ (w (k + 1))) := by
    intro k
    simp only [D, sum_range_succ]
  have hDmono' : ∀ k d, D k ≤ D (k + d) ∧ d ≤ D (k + d) - D k ∧ D (k + d) - D k ≤ d * g' := by
    intro k d
    induction d with
    | zero => simp
    | succ d ih =>
      have hb := hd (w (k + d))
      rw [← hw (k + d)] at hb
      have hs := hDstep (k + d)
      rw [show k + (d + 1) = k + d + 1 by omega, hs]
      have e : (d + 1) * g' = d * g' + g' := by ring
      refine ⟨by omega, by omega, ?_⟩
      rw [e]; omega
  have hDmono : ∀ k l, k ≤ l → D k ≤ D l ∧ l - k ≤ D l - D k ∧ D l - D k ≤ (l - k) * g' := by
    intro k l hkl
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
    simpa using hDmono' k d
  -- positions along the walk
  have hpos : ∀ k, ∃ c : ℤ, ((ρ (w k) : ℕ) : ℤ) = ρ (w 0) - D k + c * m := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp [D]⟩
    | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      have hs : ((D (k + 1) : ℕ) : ℤ) = D k + (back m (ρ (w k)) (ρ (w (k + 1))) : ℕ) := by
        rw [hDstep k]; push_cast; ring
      rcases back_int_cases m (ρ (w k)) (ρ (w (k + 1))) (hρ _) with h | h
      · exact ⟨c, by rw [hs, h]; linear_combination hc⟩
      · exact ⟨c + 1, by rw [hs, h]; linear_combination hc⟩
  -- two of the `r + 2` first positions coincide
  have key : ∀ k l : ℕ, k < l → l ≤ r + 1 → w k = w l → False := by
    intro k l hkl hl heq
    obtain ⟨ck, hck⟩ := hpos k
    obtain ⟨cl, hcl⟩ := hpos l
    rw [heq] at hck
    have hdiff : ((D l : ℕ) : ℤ) - D k = (cl - ck) * m := by linear_combination hcl - hck
    have hdvd : (m : ℤ) ∣ ((D l : ℕ) : ℤ) - D k := Dvd.intro_left (cl - ck) hdiff.symm
    have hb := hDmono k l hkl.le
    have hlt : D l - D k < m := by
      calc D l - D k ≤ (l - k) * g' := hb.2.2
        _ ≤ (r + 1) * g' := Nat.mul_le_mul_right g' (by omega)
        _ < (r + 1) * (g' + 1) := by nlinarith
        _ = m := hm.symm
    have hpos' : (0 : ℤ) < ((D l : ℕ) : ℤ) - D k := by
      have := hb.1
      have := hb.2.1
      omega
    have := Int.le_of_dvd hpos' hdvd
    omega
  obtain ⟨k, l, hkl, hfkl⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (r + 2) => w k)
    (by simp)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkl) with h | h
  · exact key k l h (by omega) hfkl
  · exact key l k h (by omega) hfkl.symm

/-! ### The decomposition -/

/-- `E_q(c) = {0}` when there are no terms. -/
lemma Eset_zero_terms (q : ℕ) (c : Fin 0 → ℤ) : Eset q c = {0} := by
  ext n; simp [Eset]

/-- The high face of the decomposition, for a residue vector `ρ` with base point `A`. -/
def highFace (q Q : ℕ) {r : ℕ} (c : Fin (r + 1) → ℤ) (m : ℕ) (ρ : Fin (r + 1) → ℕ) (A : ℕ) :
    Set ℤ :=
  {n | ∃ ℓ : Fin (r + 1) → ℕ,
    n = (q : ℤ) ^ A * ∑ i, c i * (q : ℤ) ^ back m (ρ i) A * (Q : ℤ) ^ ℓ i}

/-- The low face at index `i`. -/
def lowFace (q Q : ℕ) {r : ℕ} (c : Fin (r + 1) → ℤ) (ρ : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :
    Set ℤ :=
  {n | ∃ ℓ : Fin r → ℕ, n = c i * (q : ℤ) ^ ρ i +
    ∑ j, c (i.succAbove j) * (q : ℤ) ^ ρ (i.succAbove j) * (Q : ℤ) ^ ℓ j}

lemma highFace_eq_image (q Q : ℕ) {r : ℕ} (c : Fin (r + 1) → ℤ) (m : ℕ) (ρ : Fin (r + 1) → ℕ)
    (A : ℕ) : highFace q Q c m ρ A =
      {n | ∃ n' ∈ Eset Q (fun i => c i * (q : ℤ) ^ back m (ρ i) A),
        n = ((q ^ A : ℕ) : ℤ) * n' + 0} := by
  ext n
  simp only [highFace, Eset, Set.mem_setOf_eq, add_zero, Nat.cast_pow]
  constructor
  · rintro ⟨ℓ, rfl⟩; exact ⟨_, ⟨ℓ, rfl⟩, rfl⟩
  · rintro ⟨n', ⟨ℓ, rfl⟩, rfl⟩; exact ⟨ℓ, rfl⟩

lemma lowFace_eq_shift (q Q : ℕ) {r : ℕ} (c : Fin (r + 1) → ℤ) (ρ : Fin (r + 1) → ℕ)
    (i : Fin (r + 1)) : lowFace q Q c ρ i =
      {n | n + (-(c i * (q : ℤ) ^ ρ i)) ∈
        Eset Q (fun j => c (i.succAbove j) * (q : ℤ) ^ ρ (i.succAbove j))} := by
  ext n
  simp only [lowFace, Eset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ℓ, rfl⟩; exact ⟨ℓ, by ring⟩
  · rintro ⟨ℓ, h⟩; exact ⟨ℓ, by linear_combination h⟩

/-- The decomposition of `E_q(c)` into high and low faces, given a base point `A ρ < m` for each
residue vector `ρ : Fin (r+1) → Fin m`. -/
theorem Eset_eq_iUnion_faces (q : ℕ) {m : ℕ} (hm : 1 ≤ m) {r : ℕ} (c : Fin (r + 1) → ℤ)
    (A : (Fin (r + 1) → Fin m) → ℕ) (hA : ∀ ρ, A ρ < m) :
    Eset q c = ⋃ ρ : Fin (r + 1) → Fin m,
      (highFace q (q ^ m) c m (fun i => (ρ i : ℕ)) (A ρ) ∪
        ⋃ i, lowFace q (q ^ m) c (fun i => (ρ i : ℕ)) i) := by
  ext n
  simp only [Set.mem_iUnion, Set.mem_union, highFace, lowFace, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    -- residues and quotients
    let ρ : Fin (r + 1) → Fin m := fun i => ⟨k i % m, Nat.mod_lt _ (by omega)⟩
    let ℓ : Fin (r + 1) → ℕ := fun i => k i / m
    have hk : ∀ i, k i = m * ℓ i + (ρ i : ℕ) := fun i => (Nat.div_add_mod (k i) m).symm
    refine ⟨ρ, ?_⟩
    by_cases hcase : ∀ i, (ρ i : ℕ) < A ρ → 1 ≤ ℓ i
    · -- high face
      left
      refine ⟨fun i => if (ρ i : ℕ) < A ρ then ℓ i - 1 else ℓ i, ?_⟩
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hexp : k i = A ρ + back m (ρ i) (A ρ) +
          m * (if (ρ i : ℕ) < A ρ then ℓ i - 1 else ℓ i) := by
        have h1 := hk i
        have h3 := (ρ i).2
        have h4 := hA ρ
        by_cases hlt : (ρ i : ℕ) < A ρ
        · have h2 := hcase i hlt
          have h5 : m * (ℓ i - 1) + m = m * ℓ i := by
            rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel h2]
          rw [if_pos hlt, back, if_neg (by omega)]
          omega
        · rw [if_neg hlt, back, if_pos (by omega)]
          omega
      rw [hexp, pow_add, pow_add, pow_mul, Nat.cast_pow]
      ring
    · -- low face
      right
      push_neg at hcase
      obtain ⟨i, hi, hℓ⟩ := hcase
      have hℓ0 : ℓ i = 0 := by omega
      refine ⟨i, fun j => ℓ (i.succAbove j), ?_⟩
      rw [Fin.sum_univ_succAbove _ i]
      congr 1
      · rw [hk i, hℓ0, mul_zero, zero_add]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hk (i.succAbove j), pow_add, pow_mul, Nat.cast_pow]
        ring
  · rintro ⟨ρ, ⟨ℓ, rfl⟩ | ⟨i, ℓ, rfl⟩⟩
    · refine ⟨fun i => A ρ + back m (ρ i) (A ρ) + m * ℓ i, ?_⟩
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [pow_add, pow_add, pow_mul, Nat.cast_pow]
      ring
    · refine ⟨i.insertNth (ρ i : ℕ) (fun j => (ρ (i.succAbove j) : ℕ) + m * ℓ j), ?_⟩
      rw [Fin.sum_univ_succAbove _ i]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [pow_add, pow_mul, Nat.cast_pow]
      ring

/-! ### Proposition 2.7 -/

section Main

variable {p : ℕ} [hp : Fact p.Prime]

/-- The inductive step: `E_{q₀}(c)` with `r + 1` nonzero weights, granted Proposition 2.6 and
the case of `r` weights (for all `q₀ = p^f`). -/
theorem Eset_mem_RClass_succ (h26 : Prop26 p) {r : ℕ}
    (ih : ∀ f : ℕ, 1 ≤ f → ∀ c : Fin r → ℤ, (∀ i, c i ≠ 0) →
      Eset (p ^ f) c ∈ RClass (RatFunc (ZMod p)))
    {f : ℕ} (hf : 1 ≤ f) (c : Fin (r + 1) → ℤ) (hc : ∀ i, c i ≠ 0) :
    Eset (p ^ f) c ∈ RClass (RatFunc (ZMod p)) := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = p ^ f := ⟨_, rfl⟩
  rw [← hq]
  have hq2 : 2 ≤ q := by
    rw [hq]; exact le_trans hp.out.two_le (Nat.le_self_pow (by omega) p)
  -- the total weight, the gap length `g` and the period `m = (r + 1) g`
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = ∑ i, (c i).natAbs := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ, g = 4 * C + 1 := ⟨_, rfl⟩
  have hg1 : 1 ≤ g := by omega
  have hgC : 4 * C < q ^ g := by
    calc 4 * C < g := by omega
      _ < 2 ^ g := Nat.lt_two_pow_self
      _ ≤ q ^ g := Nat.pow_le_pow_left hq2 g
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (r + 1) * g := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by rw [hm]; nlinarith
  have hgm : g ≤ m := by rw [hm]; nlinarith
  have hQ : q ^ m = p ^ (f * m) := by rw [hq, ← pow_mul]
  have hfm : 1 ≤ f * m := Nat.mul_pos (by omega) (by omega)
  -- base points from the gap lemma
  choose a ha using fun ρ : Fin (r + 1) → Fin m =>
    exists_gap hg1 hm (fun i => (ρ i : ℕ)) (fun i => (ρ i).2)
  rw [Eset_eq_iUnion_faces q hm1 c (fun ρ => (ρ (a ρ) : ℕ)) (fun ρ => (ρ (a ρ)).2)]
  apply RClass.iUnion_mem
  intro ρ
  apply RClass.union_mem
  · -- high face: Proposition 2.6 with `Q = p^(f m)` and weights `cᵢ q^{wᵢ}`
    rw [highFace_eq_image]
    apply RClass.affine_image_mem _ (pow_pos (by omega) _) 0
    rw [hQ]
    apply h26 (f * m) hfm (r + 1) _ (by omega)
    · intro i
      exact mul_ne_zero (hc i) (pow_ne_zero _ (by positivity))
    · -- `4 ∑ |cᵢ| q^{wᵢ} < q^m`
      have hw : ∀ i, back m (ρ i) (ρ (a ρ)) ≤ m - g := ha ρ
      calc 4 * ∑ i, (c i * (q : ℤ) ^ back m (ρ i) (ρ (a ρ))).natAbs
          ≤ 4 * ∑ i, (c i).natAbs * q ^ (m - g) := by
            apply Nat.mul_le_mul_left
            apply Finset.sum_le_sum
            intro i _
            rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (hw i))
        _ = 4 * C * q ^ (m - g) := by rw [hC, ← Finset.sum_mul, mul_assoc]
        _ < q ^ g * q ^ (m - g) := by
            apply Nat.mul_lt_mul_of_pos_right hgC
            exact pow_pos (by omega) _
        _ = q ^ m := by rw [← pow_add, Nat.add_sub_cancel' hgm]
        _ = p ^ (f * m) := hQ
  · -- low faces: induction hypothesis (at `Q = p^(f m)`) and a translation
    apply RClass.iUnion_mem
    intro i
    rw [lowFace_eq_shift, hQ]
    apply RClass.shift_mem
    apply ih (f * m) hfm
    intro j
    exact mul_ne_zero (hc _) (pow_ne_zero _ (by positivity))

/-- **Proposition 2.6 implies Proposition 2.7** (§2.4 of the paper). -/
theorem prop27_of_prop26 (h26 : Prop26 p) : Prop27 p := by
  intro f hf r
  revert f
  induction r with
  | zero =>
    intro f hf c hc
    rw [Eset_zero_terms]
    exact RClass.singleton_mem_ratFunc 0
  | succ r ih =>
    intro f hf c hc
    exact Eset_mem_RClass_succ h26 ih hf c hc

/-- **Proposition 2.6 implies Theorem 2.2.** -/
theorem theorem22_of_prop26 (h26 : Prop26 p) : Theorem22 p :=
  theorem22_of_prop27 (prop27_of_prop26 h26)

end Main

end ArithDyn.Derksen
