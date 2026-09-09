import ArithDyn.Derksen.Torus
import ArithDyn.Derksen.Normal
import ArithDyn.Derksen.ValuationPoint
import ArithDyn.Derksen.CoeffDescent
import ArithDyn.Derksen.Grouping
import ArithDyn.Derksen.Reconstruct
import ArithDyn.Derksen.BackwardAux

/-!
# Backward direction of the characterisation (2.x) in Proposition 2.6

Let `F = 𝔽_q`, `q = p^e`, `c : Fin r → ℤ` nonzero weights with `4 ∑|cᵢ| < q`, and `n ∈ ℤ`. If the
point `P^n = ((t + a)^n)_a` lies on the Zariski closure of the image of `ν : a ↦ (∏ᵢ (yᵢ + a)^{cᵢ})`
(i.e. every `f ∈ I = ker ν^#` vanishes at `P^n`) and `ζ^n = ζ^{∑ cᵢ}` for a generator `ζ` of `Fˣ`,
then `n ∈ E_q(c)`, i.e. `n = ∑ᵢ cᵢ q^{kᵢ}` for some `kᵢ ≥ 0`.

Outline of the proof (`mem_Eset_of_aeval_Pn_eq_zero`):
* `ν^#` and evaluation at `P^n` give a ring hom `ψ : R := im ν^# → K = F(t)` (the kernel of
  `ν^#` is killed by hypothesis); a valuation subring `B ⊇ R` of `L = F(y)` whose maximal ideal
  meets `R` in `ker ψ` (`exists_valuationSubring_of_ringHom`) lets us view the residues of `ν_a`
  and of `ψ(ν_a) = (t + a)^n` as the images of common elements `τ_a` of a field `κ` embedded in
  both the residue field `κ(B)` and `K`.
* Splitting the coordinates `yᵢ` into those in `B` (index set `S`) and those not in `B`, the
  residues of the `ν_a` satisfy the polynomial relation `N(ā) = ν̄_a · D(ā)` in `κ(B)` for all
  `a ∈ F`, with `N, D` built from the residues `ȳᵢ`, `i ∈ S` (`ratio_identity`).
* Coefficient descent to `κ` and transport to `K = F(t)` give polynomials `N₂, D₂ ∈ F[t][X]`
  with `N₂(a) = D₂(a) (t + a)^n` for all `a ∈ F`; the reconstruction lemma (Lemma 2.5) yields
  `n = ∑ dₗ qˡ` and `N₂/D₂ = ∏ (X + t^{qˡ})^{dₗ}`.
* In a common overfield `Ω` of `κ(B)` and `K` the two descriptions of `N/D` are compared by root
  multiplicities (`group_weights`), which gives `∑_{i ∈ S} cᵢ q^{kᵢ} = n` and
  `∑_{i ∈ S} cᵢ = ∑ dₗ`; the congruence `ζ^n = ζ^{∑ cᵢ}` then forces `∑_{i ∉ S} cᵢ = 0`, so that
  `n = ∑ᵢ cᵢ q^{kᵢ}` with `kᵢ = 0` for `i ∉ S`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ArithDyn.Derksen

open Polynomial

universe u

/-! ### The residue map of a valuation subring, as a total function -/

section Residue

open scoped Classical

variable {L : Type*} [Field L] (B : ValuationSubring L)

/-- The residue of `x ∈ L` in the residue field `κ(B)`, extended by `0` outside `B`. -/
noncomputable def resB (x : L) : IsLocalRing.ResidueField B :=
  if hx : x ∈ B then IsLocalRing.residue B ⟨x, hx⟩ else 0

theorem resB_of_mem {x : L} (hx : x ∈ B) : resB B x = IsLocalRing.residue B ⟨x, hx⟩ :=
  dif_pos hx

theorem resB_eq_zero_iff {x : L} (hx : x ∈ B) : resB B x = 0 ↔ B.valuation x < 1 := by
  rw [resB_of_mem B hx]
  exact residue_eq_zero_iff_valuation_lt_one B ⟨x, hx⟩

theorem resB_one : resB B 1 = 1 := by
  rw [resB_of_mem B (one_mem B)]
  exact map_one (IsLocalRing.residue B)

theorem resB_mul {x y : L} (hx : x ∈ B) (hy : y ∈ B) :
    resB B (x * y) = resB B x * resB B y := by
  rw [resB_of_mem B (mul_mem hx hy), resB_of_mem B hx, resB_of_mem B hy, ← map_mul]
  rfl

theorem resB_add {x y : L} (hx : x ∈ B) (hy : y ∈ B) :
    resB B (x + y) = resB B x + resB B y := by
  rw [resB_of_mem B (add_mem hx hy), resB_of_mem B hx, resB_of_mem B hy, ← map_add]
  rfl

theorem resB_pow {x : L} (hx : x ∈ B) (n : ℕ) : resB B (x ^ n) = resB B x ^ n := by
  rw [resB_of_mem B (pow_mem hx n), resB_of_mem B hx, ← map_pow]
  rfl

theorem resB_prod {ι : Type*} (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, f i ∈ B) :
    resB B (∏ i ∈ s, f i) = ∏ i ∈ s, resB B (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [resB_one]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, f i ∈ B := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      resB_mul B (hf a (Finset.mem_insert_self a s)) (prod_mem hs), ih hs]

theorem inv_mem_of_not_mem {x : L} (hx : x ∉ B) : x⁻¹ ∈ B :=
  (B.mem_or_inv_mem x).resolve_left hx

theorem valuation_inv_lt_one_of_not_mem {x : L} (hx0 : x ≠ 0) (hx : x ∉ B) :
    B.valuation x⁻¹ < 1 := by
  rw [map_inv₀, inv_lt_one₀ ((Valuation.pos_iff _).2 hx0)]
  exact not_le.1 fun h => hx (B.mem_of_valuation_le_one x h)

theorem resB_inv_eq_zero {x : L} (hx0 : x ≠ 0) (hx : x ∉ B) : resB B x⁻¹ = 0 :=
  (resB_eq_zero_iff B (inv_mem_of_not_mem B hx)).2 (valuation_inv_lt_one_of_not_mem B hx0 hx)

end Residue

/-! ### The ratio identity in the residue field (steps 5–7 of the proof) -/

section Ratio

open scoped Classical

variable {L : Type*} [Field L] (B : ValuationSubring L) {ι : Type*} (y : ι → L) (c : ι → ℤ)

/-- The unit-like factor `g i a = a + yᵢ` (`yᵢ ∈ B`) or `1 + a yᵢ⁻¹` (`yᵢ ∉ B`). -/
noncomputable def gfac (a : L) (i : ι) : L := if y i ∈ B then a + y i else 1 + a * (y i)⁻¹

/-- The factor `h i = 1` (`yᵢ ∈ B`) or `yᵢ` (`yᵢ ∉ B`), independent of `a`. -/
noncomputable def hfac (i : ι) : L := if y i ∈ B then 1 else y i

theorem gfac_mem {a : L} (ha : a ∈ B) (i : ι) : gfac B y a i ∈ B := by
  unfold gfac
  split_ifs with h
  · exact add_mem ha h
  · exact add_mem (one_mem B) (mul_mem ha (inv_mem_of_not_mem B h))

theorem gfac_ne_zero (hy : ∀ i, y i ≠ 0) {a : L} (ha' : ∀ i, y i + a ≠ 0) (i : ι) :
    gfac B y a i ≠ 0 := by
  unfold gfac
  split_ifs with h
  · rw [add_comm]; exact ha' i
  · have : 1 + a * (y i)⁻¹ = (y i)⁻¹ * (y i + a) := by
      rw [mul_add, inv_mul_cancel₀ (hy i), mul_comm]
    rw [this]
    exact mul_ne_zero (inv_ne_zero (hy i)) (ha' i)

theorem hfac_mul_gfac (hy : ∀ i, y i ≠ 0) (a : L) (i : ι) :
    hfac B y i * gfac B y a i = y i + a := by
  unfold hfac gfac
  split_ifs with h
  · rw [one_mul, add_comm]
  · rw [mul_add, mul_one, mul_comm a, ← mul_assoc, mul_inv_cancel₀ (hy i), one_mul]

theorem resB_gfac (hy : ∀ i, y i ≠ 0) {a : L} (ha : a ∈ B) (i : ι) :
    resB B (gfac B y a i) = if y i ∈ B then resB B a + resB B (y i) else 1 := by
  unfold gfac
  split_ifs with h
  · exact resB_add B ha h
  · rw [resB_add B (one_mem B) (mul_mem ha (inv_mem_of_not_mem B h)), resB_one,
      resB_mul B ha (inv_mem_of_not_mem B h), resB_inv_eq_zero B (hy i) h, mul_zero, add_zero]

variable [Fintype ι]

/-- The set of indices `i` with `y i ∈ B` ("finite coordinates"). -/
noncomputable def Sfin : Finset ι := Finset.univ.filter (fun i => y i ∈ B)

/-- `Fnum x = ∏_{i ∈ S, cᵢ > 0} (x + ȳᵢ)^{cᵢ}` in `κ(B)`. -/
noncomputable def Fnum (x : IsLocalRing.ResidueField B) : IsLocalRing.ResidueField B :=
  ∏ i ∈ (Sfin B y).filter (fun i => 0 < c i), (x + resB B (y i)) ^ (c i).toNat

/-- `Fden x = ∏_{i ∈ S, cᵢ < 0} (x + ȳᵢ)^{-cᵢ}` in `κ(B)`. -/
noncomputable def Fden (x : IsLocalRing.ResidueField B) : IsLocalRing.ResidueField B :=
  ∏ i ∈ (Sfin B y).filter (fun i => c i < 0), (x + resB B (y i)) ^ (-(c i)).toNat

/-- `Gnum a = ∏_{cᵢ > 0} g i a ^{cᵢ}` in `L`. -/
noncomputable def Gnum (a : L) : L :=
  ∏ i ∈ Finset.univ.filter (fun i => 0 < c i), gfac B y a i ^ (c i).toNat

/-- `Gden a = ∏_{cᵢ < 0} g i a ^{-cᵢ}` in `L`. -/
noncomputable def Gden (a : L) : L :=
  ∏ i ∈ Finset.univ.filter (fun i => c i < 0), gfac B y a i ^ (-(c i)).toNat

theorem Gnum_mem {a : L} (ha : a ∈ B) : Gnum B y c a ∈ B :=
  prod_mem fun i _ => pow_mem (gfac_mem B y ha i) _

theorem Gden_mem {a : L} (ha : a ∈ B) : Gden B y c a ∈ B :=
  prod_mem fun i _ => pow_mem (gfac_mem B y ha i) _

theorem Gden_ne_zero (hy : ∀ i, y i ≠ 0) {a : L} (ha' : ∀ i, y i + a ≠ 0) :
    Gden B y c a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (gfac_ne_zero B y hy ha' i)

/-- `ν_a · Gden a = Y · Gnum a` with `Y = ∏ᵢ h i ^{cᵢ}` independent of `a`. -/
theorem nu_mul_Gden (hy : ∀ i, y i ≠ 0) {a : L} (ha' : ∀ i, y i + a ≠ 0) :
    (∏ i, (y i + a) ^ c i) * Gden B y c a = (∏ i, hfac B y i ^ c i) * Gnum B y c a := by
  have h1 : ∏ i, (y i + a) ^ c i = (∏ i, hfac B y i ^ c i) * ∏ i, gfac B y a i ^ c i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [← mul_zpow, hfac_mul_gfac B y hy a i]
  have h2 : ∏ i, gfac B y a i ^ c i = Gnum B y c a / Gden B y c a :=
    prod_zpow_eq_div Finset.univ (fun i => gfac B y a i) c
  rw [h1, h2, mul_assoc, div_mul_cancel₀ _ (Gden_ne_zero B y c hy ha')]

theorem resB_Gnum (hy : ∀ i, y i ≠ 0) {a : L} (ha : a ∈ B) :
    resB B (Gnum B y c a) = Fnum B y c (resB B a) := by
  unfold Gnum Fnum Sfin
  rw [resB_prod B _ _ (fun i _ => pow_mem (gfac_mem B y ha i) _), Finset.filter_filter,
    Finset.prod_filter, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [resB_pow B (gfac_mem B y ha i), resB_gfac B y hy ha i]
  by_cases h1 : 0 < c i <;> by_cases h2 : y i ∈ B <;> simp [h1, h2]

theorem resB_Gden (hy : ∀ i, y i ≠ 0) {a : L} (ha : a ∈ B) :
    resB B (Gden B y c a) = Fden B y c (resB B a) := by
  unfold Gden Fden Sfin
  rw [resB_prod B _ _ (fun i _ => pow_mem (gfac_mem B y ha i) _), Finset.filter_filter,
    Finset.prod_filter, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [resB_pow B (gfac_mem B y ha i), resB_gfac B y hy ha i]
  by_cases h1 : c i < 0 <;> by_cases h2 : y i ∈ B <;> simp [h1, h2]

/-- **The ratio identity.** For `a, b ∈ B` with `ν_a, ν_b ∈ B`,
`ν̄_a · Fden ā · Fnum b̄ = ν̄_b · Fnum ā · Fden b̄` in `κ(B)`. -/
theorem ratio_identity (hy : ∀ i, y i ≠ 0) {a b : L} (ha : a ∈ B) (hb : b ∈ B)
    (ha' : ∀ i, y i + a ≠ 0) (hb' : ∀ i, y i + b ≠ 0)
    (hνa : ∏ i, (y i + a) ^ c i ∈ B) (hνb : ∏ i, (y i + b) ^ c i ∈ B) :
    resB B (∏ i, (y i + a) ^ c i) * Fden B y c (resB B a) * Fnum B y c (resB B b) =
      resB B (∏ i, (y i + b) ^ c i) * Fnum B y c (resB B a) * Fden B y c (resB B b) := by
  have hL : (∏ i, (y i + a) ^ c i) * Gden B y c a * Gnum B y c b =
      (∏ i, (y i + b) ^ c i) * Gden B y c b * Gnum B y c a := by
    rw [nu_mul_Gden B y c hy ha', nu_mul_Gden B y c hy hb']
    ring
  have h := congrArg (resB B) hL
  rw [resB_mul B (mul_mem hνa (Gden_mem B y c ha)) (Gnum_mem B y c hb),
    resB_mul B hνa (Gden_mem B y c ha),
    resB_mul B (mul_mem hνb (Gden_mem B y c hb)) (Gnum_mem B y c ha),
    resB_mul B hνb (Gden_mem B y c hb),
    resB_Gnum B y c hy ha, resB_Gnum B y c hy hb, resB_Gden B y c hy ha,
    resB_Gden B y c hy hb] at h
  rw [h]
  ring

/-! ### The polynomials `N`, `D` over the residue field (step 8) -/

/-- `N = n₀ · ∏_{i ∈ S, cᵢ > 0} (X + ȳᵢ)^{cᵢ}`. -/
noncomputable def Npoly (n₀ : IsLocalRing.ResidueField B) : Polynomial (IsLocalRing.ResidueField B) :=
  C n₀ * ∏ i ∈ (Sfin B y).filter (fun i => 0 < c i), (X + C (resB B (y i))) ^ (c i).toNat

/-- `D = d₀ · ∏_{i ∈ S, cᵢ < 0} (X + ȳᵢ)^{-cᵢ}`. -/
noncomputable def Dpoly (d₀ : IsLocalRing.ResidueField B) : Polynomial (IsLocalRing.ResidueField B) :=
  C d₀ * ∏ i ∈ (Sfin B y).filter (fun i => c i < 0), (X + C (resB B (y i))) ^ (-(c i)).toNat

theorem eval_Npoly (n₀ x : IsLocalRing.ResidueField B) :
    (Npoly B y c n₀).eval x = n₀ * Fnum B y c x := by
  unfold Npoly Fnum
  rw [eval_mul, eval_C, eval_prod]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [eval_pow, eval_add, eval_X, eval_C]

theorem eval_Dpoly (d₀ x : IsLocalRing.ResidueField B) :
    (Dpoly B y c d₀).eval x = d₀ * Fden B y c x := by
  unfold Dpoly Fden
  rw [eval_mul, eval_C, eval_prod]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [eval_pow, eval_add, eval_X, eval_C]

theorem natDegree_Npoly_le (n₀ : IsLocalRing.ResidueField B) :
    (Npoly B y c n₀).natDegree ≤ ∑ i ∈ (Sfin B y).filter (fun i => 0 < c i), (c i).toNat := by
  unfold Npoly
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  refine natDegree_pow_le.trans ?_
  rw [natDegree_X_add_C, mul_one]

theorem natDegree_Dpoly_le (d₀ : IsLocalRing.ResidueField B) :
    (Dpoly B y c d₀).natDegree ≤ ∑ i ∈ (Sfin B y).filter (fun i => c i < 0), (-(c i)).toNat := by
  unfold Dpoly
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  refine natDegree_pow_le.trans ?_
  rw [natDegree_X_add_C, mul_one]

theorem Dpoly_ne_zero {d₀ : IsLocalRing.ResidueField B} (hd₀ : d₀ ≠ 0) : Dpoly B y c d₀ ≠ 0 :=
  mul_ne_zero (C_ne_zero.2 hd₀) (prod_linear_pow_ne_zero _ _ _)

/-- The polynomial relation `N(ā) = ν̄_a · D(ā)` (with `N, D` normalised at a base point `b₀`). -/
theorem Npoly_eval_eq (hy : ∀ i, y i ≠ 0) {a b₀ : L} (ha : a ∈ B) (hb₀ : b₀ ∈ B)
    (ha' : ∀ i, y i + a ≠ 0) (hb₀' : ∀ i, y i + b₀ ≠ 0)
    (hνa : ∏ i, (y i + a) ^ c i ∈ B) (hνb₀ : ∏ i, (y i + b₀) ^ c i ∈ B) :
    (Npoly B y c (resB B (∏ i, (y i + b₀) ^ c i) * Fden B y c (resB B b₀))).eval (resB B a) =
      resB B (∏ i, (y i + a) ^ c i) *
        (Dpoly B y c (Fnum B y c (resB B b₀))).eval (resB B a) := by
  rw [eval_Npoly, eval_Dpoly]
  have h := ratio_identity B y c hy ha hb₀ ha' hb₀' hνa hνb₀
  linear_combination -h

end Ratio

/-- The degree bound `∑_{cᵢ>0} cᵢ + ∑_{cᵢ<0} (-cᵢ) ≤ ∑ᵢ |cᵢ|` (over any subset `S`). -/
theorem sum_toNat_add_sum_toNat_neg_le {ι : Type*} [Fintype ι] (S : Finset ι) (c : ι → ℤ) :
    ∑ i ∈ S.filter (fun i => 0 < c i), (c i).toNat +
        ∑ i ∈ S.filter (fun i => c i < 0), (-(c i)).toNat ≤ ∑ i, (c i).natAbs := by
  calc ∑ i ∈ S.filter (fun i => 0 < c i), (c i).toNat +
        ∑ i ∈ S.filter (fun i => c i < 0), (-(c i)).toNat
      ≤ ∑ i, (c i).toNat + ∑ i, (-(c i)).toNat :=
        add_le_add (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
          (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
    _ = ∑ i, ((c i).toNat + (-(c i)).toNat) := Finset.sum_add_distrib.symm
    _ = ∑ i, (c i).natAbs := Finset.sum_congr rfl fun i _ => Int.toNat_add_toNat_neg_eq_natAbs _

/-! ### Transport of the two descriptions of `N/D` to `Ω(X)` (step 12) -/

/-- From `N · D₀ = N₀ · D` (over `κ(B)`, with `N₀, D₀` over `κ`) to the equality of quotients
in `Ω(X)`. -/
theorem transport_descent {κ κB Ω : Type*} [Field κ] [Field κB] [Field Ω] (ι₁ : κ →+* κB)
    (j₁ : κB →+* Ω) (N D : Polynomial κB) (N₀ D₀ : Polynomial κ) (hD : D ≠ 0) (hD₀ : D₀ ≠ 0)
    (hND : N * D₀.map ι₁ = N₀.map ι₁ * D) :
    algebraMap (Polynomial Ω) (RatFunc Ω) (N₀.map (j₁.comp ι₁)) /
        algebraMap (Polynomial Ω) (RatFunc Ω) (D₀.map (j₁.comp ι₁)) =
      algebraMap (Polynomial Ω) (RatFunc Ω) (N.map j₁) /
        algebraMap (Polynomial Ω) (RatFunc Ω) (D.map j₁) := by
  have hinj : Function.Injective (algebraMap (Polynomial Ω) (RatFunc Ω)) :=
    IsFractionRing.injective (Polynomial Ω) (RatFunc Ω)
  have h1 : algebraMap (Polynomial Ω) (RatFunc Ω) (D₀.map (j₁.comp ι₁)) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 ((Polynomial.map_ne_zero_iff (j₁.comp ι₁).injective).2 hD₀)
  have h2 : algebraMap (Polynomial Ω) (RatFunc Ω) (D.map j₁) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 ((Polynomial.map_ne_zero_iff j₁.injective).2 hD)
  rw [div_eq_div_iff h1 h2, ← map_mul, ← map_mul]
  congr 1
  have h := congrArg (Polynomial.map j₁) hND
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_map] at h
  exact h.symm

section Transport

open scoped Classical

variable {L : Type*} [Field L] (B : ValuationSubring L) {ι : Type*} [Fintype ι] (y : ι → L)
  (c : ι → ℤ)

/-- `N/D` in `Ω(X)` as `κ' · ∏_{i ∈ S} (X + ȳᵢ)^{cᵢ}`. -/
theorem map_Npoly_div_map_Dpoly {Ω : Type*} [Field Ω] (j₁ : IsLocalRing.ResidueField B →+* Ω)
    (n₀ d₀ : IsLocalRing.ResidueField B) :
    algebraMap (Polynomial Ω) (RatFunc Ω) ((Npoly B y c n₀).map j₁) /
        algebraMap (Polynomial Ω) (RatFunc Ω) ((Dpoly B y c d₀).map j₁) =
      algebraMap (Polynomial Ω) (RatFunc Ω) (C (j₁ n₀ / j₁ d₀)) *
        ∏ i ∈ Sfin B y,
          algebraMap (Polynomial Ω) (RatFunc Ω) (X + C (j₁ (resB B (y i)))) ^ c i := by
  rw [prod_zpow_eq_div (Sfin B y)
    (fun i => algebraMap (Polynomial Ω) (RatFunc Ω) (X + C (j₁ (resB B (y i))))) c]
  unfold Npoly Dpoly
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_X, map_mul, map_prod, map_pow, RatFunc.algebraMap_C]
  rw [map_div₀, mul_div_mul_comm]

end Transport

/-- Transport of the conclusion of the reconstruction lemma from `Frac(F[t][X])` to `Ω(X)`
along `j₂ : K → Ω`. -/
theorem transport_reconstruct {F : Type*} [Field F] {K : Type*} [Field K]
    [Algebra (Polynomial F) K] [IsFractionRing (Polynomial F) K] {Ω : Type*} [Field Ω]
    (j₂ : K →+* Ω) (N₂ D₂ : Polynomial (Polynomial F)) (N₀K D₀K : Polynomial K) (β : K)
    (hβ : β ≠ 0) (hN₂ : N₂.map (algebraMap (Polynomial F) K) = C β * N₀K)
    (hD₂ : D₂.map (algebraMap (Polynomial F) K) = C β * D₀K) (m L : ℕ) (d : ℕ → ℤ)
    (hprod : algebraMap _ (ΩB F) N₂ / algebraMap _ (ΩB F) D₂ =
      ∏ ℓ ∈ Finset.range L,
        algebraMap _ (ΩB F) (X + C (Polynomial.X ^ m ^ ℓ) : Polynomial (Polynomial F)) ^ d ℓ) :
    algebraMap (Polynomial Ω) (RatFunc Ω) (N₀K.map j₂) /
        algebraMap (Polynomial Ω) (RatFunc Ω) (D₀K.map j₂) =
      ∏ ℓ ∈ Finset.range L, algebraMap (Polynomial Ω) (RatFunc Ω)
        (X + C (j₂ (algebraMap (Polynomial F) K (Polynomial.X ^ m ^ ℓ)))) ^ d ℓ := by
  obtain ⟨g, hg⟩ : ∃ g : Polynomial (Polynomial F) →+* RatFunc Ω,
      g = (algebraMap (Polynomial Ω) (RatFunc Ω)).comp
        (Polynomial.mapRingHom (j₂.comp (algebraMap (Polynomial F) K))) := ⟨_, rfl⟩
  have hginj : Function.Injective g := by
    rw [hg]
    exact (IsFractionRing.injective (Polynomial Ω) (RatFunc Ω)).comp
      (Polynomial.map_injective _ (j₂.injective.comp (IsFractionRing.injective (Polynomial F) K)))
  have hΘ := congrArg (IsFractionRing.lift (A := Polynomial (Polynomial F)) (K := ΩB F) hginj)
    hprod
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap, map_prod] at hΘ
  simp_rw [map_zpow₀, IsFractionRing.lift_algebraMap] at hΘ
  have hgN : g N₂ = algebraMap (Polynomial Ω) (RatFunc Ω) (C (j₂ β)) *
      algebraMap (Polynomial Ω) (RatFunc Ω) (N₀K.map j₂) := by
    rw [hg, RingHom.comp_apply, Polynomial.coe_mapRingHom, ← Polynomial.map_map, hN₂,
      Polynomial.map_mul, Polynomial.map_C, map_mul]
  have hgD : g D₂ = algebraMap (Polynomial Ω) (RatFunc Ω) (C (j₂ β)) *
      algebraMap (Polynomial Ω) (RatFunc Ω) (D₀K.map j₂) := by
    rw [hg, RingHom.comp_apply, Polynomial.coe_mapRingHom, ← Polynomial.map_map, hD₂,
      Polynomial.map_mul, Polynomial.map_C, map_mul]
  have hgX : ∀ ℓ, g (X + C (Polynomial.X ^ m ^ ℓ) : Polynomial (Polynomial F)) =
      algebraMap (Polynomial Ω) (RatFunc Ω)
        (X + C (j₂ (algebraMap (Polynomial F) K (Polynomial.X ^ m ^ ℓ)))) := by
    intro ℓ
    rw [hg, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_C, RingHom.comp_apply]
  have hC : algebraMap (Polynomial Ω) (RatFunc Ω) (C (j₂ β)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Ω) (RatFunc Ω))).2
      (C_ne_zero.2 ((map_ne_zero j₂).2 hβ))
  rw [hgN, hgD, mul_div_mul_left _ _ hC] at hΘ
  rw [hΘ]
  exact Finset.prod_congr rfl fun ℓ _ => by rw [hgX]

/-! ### Clearing denominators over `F[t]` (step 10) -/

/-- From a relation `N₀(a) = (t + a)^n D₀(a)` over `K = F(t)` to one over `F[t]`, keeping track of
degrees and of the constant `β` relating the polynomials. -/
theorem exists_clear_pair {F : Type*} [Field F] (N₀K D₀K : Polynomial (RatFunc F))
    (hD₀K : D₀K ≠ 0) (n : ℤ) (A : Finset F)
    (hrel : ∀ a ∈ A, N₀K.eval (algebraMap F (RatFunc F) a) =
      Pn n a * D₀K.eval (algebraMap F (RatFunc F) a)) :
    ∃ (N₂ D₂ : Polynomial (Polynomial F)) (β : RatFunc F), β ≠ 0 ∧
      N₂.map (algebraMap (Polynomial F) (RatFunc F)) = C β * N₀K ∧
      D₂.map (algebraMap (Polynomial F) (RatFunc F)) = C β * D₀K ∧ D₂ ≠ 0 ∧
      N₂.natDegree = N₀K.natDegree ∧ D₂.natDegree = D₀K.natDegree ∧
      ∀ a ∈ A, algebraMap (Polynomial F) (RatFunc F) (N₂.eval (C a)) =
        algebraMap (Polynomial F) (RatFunc F) (D₂.eval (C a)) *
          algebraMap (Polynomial F) (RatFunc F) (Polynomial.X + C a) ^ n := by
  obtain ⟨N₁, b₁, hb₁, hN₁⟩ := exists_clear' (F := F) (K := RatFunc F) N₀K
  obtain ⟨D₁, b₂, hb₂, hD₁⟩ := exists_clear' (F := F) (K := RatFunc F) D₀K
  have hinj : Function.Injective (algebraMap (Polynomial F) (RatFunc F)) :=
    IsFractionRing.injective (Polynomial F) (RatFunc F)
  have hβ : algebraMap (Polynomial F) (RatFunc F) (b₁ * b₂) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (mul_ne_zero hb₁ hb₂)
  have hN₂ : (C b₂ * N₁).map (algebraMap (Polynomial F) (RatFunc F)) =
      C (algebraMap (Polynomial F) (RatFunc F) (b₁ * b₂)) * N₀K := by
    rw [Polynomial.map_mul, Polynomial.map_C, hN₁, ← mul_assoc, ← C_mul, ← map_mul, mul_comm b₂]
  have hD₂ : (C b₁ * D₁).map (algebraMap (Polynomial F) (RatFunc F)) =
      C (algebraMap (Polynomial F) (RatFunc F) (b₁ * b₂)) * D₀K := by
    rw [Polynomial.map_mul, Polynomial.map_C, hD₁, ← mul_assoc, ← C_mul, ← map_mul]
  have hCa : ∀ a : F, algebraMap (Polynomial F) (RatFunc F) (C a) = algebraMap F (RatFunc F) a := by
    intro a
    rw [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  refine ⟨C b₂ * N₁, C b₁ * D₁, algebraMap (Polynomial F) (RatFunc F) (b₁ * b₂), hβ, hN₂, hD₂,
    ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, Polynomial.map_zero] at hD₂
    exact hD₀K ((mul_eq_zero.1 hD₂.symm).resolve_left (C_ne_zero.2 hβ))
  · rw [← natDegree_map_eq_of_injective hinj, hN₂, natDegree_C_mul hβ]
  · rw [← natDegree_map_eq_of_injective hinj, hD₂, natDegree_C_mul hβ]
  · intro a ha
    have e1 : algebraMap (Polynomial F) (RatFunc F) ((C b₂ * N₁).eval (C a)) =
        algebraMap (Polynomial F) (RatFunc F) (b₁ * b₂) *
          N₀K.eval (algebraMap F (RatFunc F) a) := by
      rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hN₂, eval_mul, eval_C, hCa]
    have e2 : algebraMap (Polynomial F) (RatFunc F) ((C b₁ * D₁).eval (C a)) =
        algebraMap (Polynomial F) (RatFunc F) (b₁ * b₂) *
          D₀K.eval (algebraMap F (RatFunc F) a) := by
      rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hD₂, eval_mul, eval_C, hCa]
    rw [e1, e2, hrel a ha]
    unfold Pn
    ring

/-! ### Choice of a base point, the congruence, and the final arithmetic (steps 6, 13–15) -/

/-- If `S` has fewer elements than `F`, some `b₀ ∈ F` avoids the finitely many roots `-wᵢ`. -/
theorem exists_good_base {F κB : Type*} [Fintype F] [Field κB] {ι : Type*} (S : Finset ι)
    (f : F → κB) (hf : Function.Injective f) (w : ι → κB) (hS : S.card < Fintype.card F) :
    ∃ b₀ : F, ∀ i ∈ S, f b₀ + w i ≠ 0 := by
  classical
  by_contra h
  have h' : ∀ b₀ : F, ∃ i ∈ S, f b₀ + w i = 0 := fun b₀ => by
    by_contra h2
    exact h ⟨b₀, fun i hi hi0 => h2 ⟨i, hi, hi0⟩⟩
  have hsub : (Finset.univ : Finset F) ⊆
      S.biUnion (fun i => Finset.univ.filter (fun a => f a + w i = 0)) := by
    intro a _
    obtain ⟨i, hi, hia⟩ := h' a
    exact Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_filter.2 ⟨Finset.mem_univ a, hia⟩⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hle : ∑ i ∈ S, (Finset.univ.filter (fun a => f a + w i = 0)).card ≤ ∑ i ∈ S, 1 := by
    refine Finset.sum_le_sum fun i _ => Finset.card_le_one.2 fun a ha b hb => ?_
    apply hf
    have ha' := (Finset.mem_filter.1 ha).2
    have hb' := (Finset.mem_filter.1 hb).2
    linear_combination ha' - hb'
  rw [Finset.sum_const, smul_eq_mul, mul_one] at hle
  rw [Finset.card_univ] at hcard
  omega

/-- `ζ^a = ζ^b` for an element of order `m ≠ 0` of a field gives `a ≡ b (mod m)`. -/
theorem modEq_of_zpow_eq {F : Type*} [Field F] {ζ : F} {m : ℕ} (hm : m ≠ 0) (hζ : orderOf ζ = m)
    {a b : ℤ} (h : ζ ^ a = ζ ^ b) : a ≡ b [ZMOD (m : ℤ)] := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at hζ
    exact hm hζ.symm
  have hu : (Units.mk0 ζ hζ0) ^ a = (Units.mk0 ζ hζ0) ^ b :=
    Units.ext (by rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0]; exact h)
  rw [zpow_eq_zpow_iff_modEq, ← orderOf_units, Units.val_mk0, hζ] at hu
  exact hu

/-- The final arithmetic: from `n = ∑ dₗ qˡ`, `∑_{i ∈ S} cᵢ q^{kᵢ} = ∑ dₗ qˡ`, `∑_{i ∈ S} cᵢ = ∑ dₗ`
and `n ≡ ∑ᵢ cᵢ (mod q - 1)` with `∑ |cᵢ| < q - 1` we get `n ∈ E_q(c)`. -/
theorem final_arith {r : ℕ} (c : Fin r → ℤ) (q : ℕ) (hq : 2 ≤ q) (n : ℤ) (S : Finset (Fin r))
    (Lr : ℕ) (d : ℕ → ℤ) (hsum : n = ∑ ℓ ∈ Finset.range Lr, d ℓ * (q : ℤ) ^ ℓ)
    (kk : Fin r → ℕ)
    (hkk : ∑ i ∈ S, c i * (q : ℤ) ^ kk i = ∑ ℓ ∈ Finset.range Lr, d ℓ * (q : ℤ) ^ ℓ)
    (hkk1 : ∑ i ∈ S, c i = ∑ ℓ ∈ Finset.range Lr, d ℓ)
    (hmod : n ≡ ∑ i, c i [ZMOD ((q - 1 : ℕ) : ℤ)])
    (hCq : ∑ i, (c i).natAbs < q - 1) : n ∈ Eset q c := by
  classical
  have h1 : ∑ ℓ ∈ Finset.range Lr, d ℓ * (q : ℤ) ^ ℓ ≡
      ∑ ℓ ∈ Finset.range Lr, d ℓ [ZMOD ((q : ℤ) - 1)] :=
    sum_mul_pow_modEq _ d (fun ℓ => ℓ) (q : ℤ)
  have hq1 : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hq1] at hmod
  have h2 : ∑ i, c i ≡ ∑ i ∈ S, c i [ZMOD ((q : ℤ) - 1)] := by
    refine hmod.symm.trans ?_
    rw [hsum, hkk1]
    exact h1
  have h3 : ∑ i ∈ S, c i + ∑ i ∈ Sᶜ, c i = ∑ i, c i := Finset.sum_add_sum_compl S c
  have hdvd : ((q - 1 : ℕ) : ℤ) ∣ ∑ i ∈ Sᶜ, c i := by
    rw [hq1]
    have := h2.symm.dvd
    rwa [← h3, add_sub_cancel_left] at this
  have habs : (∑ i ∈ Sᶜ, c i).natAbs < q - 1 := by
    have hle : ((∑ i ∈ Sᶜ, c i).natAbs : ℤ) ≤ ((∑ i, (c i).natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, Nat.cast_sum]
      calc |∑ i ∈ Sᶜ, c i| ≤ ∑ i ∈ Sᶜ, |c i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |c i| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => abs_nonneg _
        _ = ∑ i, ((c i).natAbs : ℤ) := Finset.sum_congr rfl fun i _ => (Int.natCast_natAbs _).symm
    have : (∑ i ∈ Sᶜ, c i).natAbs ≤ ∑ i, (c i).natAbs := by exact_mod_cast hle
    omega
  have h0 : ∑ i ∈ Sᶜ, c i = 0 := eq_zero_of_dvd_of_natAbs_lt hdvd habs
  show ∃ k : Fin r → ℕ, n = ∑ i, c i * (q : ℤ) ^ k i
  refine ⟨fun i => if i ∈ S then kk i else 0, ?_⟩
  rw [← Finset.sum_add_sum_compl S]
  have e1 : ∑ i ∈ S, c i * (q : ℤ) ^ (if i ∈ S then kk i else 0) =
      ∑ i ∈ S, c i * (q : ℤ) ^ kk i :=
    Finset.sum_congr rfl fun i hi => by rw [if_pos hi]
  have e2 : ∑ i ∈ Sᶜ, c i * (q : ℤ) ^ (if i ∈ S then kk i else 0) = ∑ i ∈ Sᶜ, c i :=
    Finset.sum_congr rfl fun i hi => by rw [if_neg (Finset.mem_compl.1 hi), pow_zero, mul_one]
  rw [e1, e2, hkk, h0, add_zero]
  exact hsum

/-! ### The valuation point attached to `P^n` (steps 1–4) -/

section Main

variable {F : Type u} [Field F] [Fintype F] {r : ℕ} (c : Fin r → ℤ)

omit [Fintype F] in
theorem νsharp_X (a : F) : νsharp c (MvPolynomial.X a) = νpt c a :=
  MvPolynomial.aeval_X _ _

omit [Fintype F] in
theorem νsharp_C (a : F) : νsharp c (MvPolynomial.C a) = algebraMap F (Lfield F r) a :=
  MvPolynomial.aeval_C _ _

omit [Fintype F] in
/-- Evaluation at `P^n` factors through `R = im ν^#` when every `f ∈ I = ker ν^#` vanishes at
`P^n`: there is `ψ : R →+* K` with `ψ (ν^# x) = x (P^n)`. -/
theorem exists_psi (n : ℤ) (hV : ∀ f ∈ torusIdeal (F := F) c, MvPolynomial.aeval (Pn n) f = 0) :
    ∃ ψ : (νsharp (F := F) c).toRingHom.range →+* RatFunc F,
      ∀ x : MvPolynomial F F, ψ ⟨νsharp c x, ⟨x, rfl⟩⟩ = MvPolynomial.aeval (Pn n) x := by
  have hsurj : Function.Surjective (νsharp (F := F) c).toRingHom.rangeRestrict :=
    RingHom.rangeRestrict_surjective _
  have hker : RingHom.ker (νsharp (F := F) c).toRingHom.rangeRestrict ≤
      RingHom.ker (MvPolynomial.aeval (Pn n) : MvPolynomial F F →ₐ[F] RatFunc F).toRingHom := by
    intro x hx
    rw [RingHom.ker_rangeRestrict] at hx
    exact RingHom.mem_ker.2 (hV x hx)
  refine ⟨(νsharp (F := F) c).toRingHom.rangeRestrict.liftOfSurjective hsurj ⟨_, hker⟩,
    fun x => ?_⟩
  exact RingHom.liftOfSurjective_comp_apply (νsharp (F := F) c).toRingHom.rangeRestrict hsurj
    ⟨_, hker⟩ x

omit [Fintype F] in
set_option maxHeartbeats 800000 in
/-- **The valuation point.** A valuation subring `B` of `L = F(y)` containing `R = im ν^#`, a
field `κ` embedded in the residue field `κ(B)` (by `ι₁`) and in `K = F(t)` (by `ι₂`), and
elements `τ_a, a_κ ∈ κ` with `ι₁ τ_a = ν̄_a`, `ι₂ τ_a = (t + a)^n`, `ι₁ a_κ = ā`, `ι₂ a_κ = a`. -/
theorem exists_valuation_point_data (n : ℤ)
    (hV : ∀ f ∈ torusIdeal (F := F) c, MvPolynomial.aeval (Pn n) f = 0) :
    ∃ (B : ValuationSubring (Lfield F r)) (κ : Type u) (_ : Field κ)
      (ι₁ : κ →+* IsLocalRing.ResidueField B) (ι₂ : κ →+* RatFunc F) (τκ aκ : F → κ),
      Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      (∀ a, νpt c a ∈ B) ∧ (∀ a, algebraMap F (Lfield F r) a ∈ B) ∧
      (∀ a, ι₁ (τκ a) = resB B (νpt c a)) ∧ (∀ a, ι₂ (τκ a) = Pn n a) ∧
      (∀ a, ι₁ (aκ a) = resB B (algebraMap F (Lfield F r) a)) ∧
      (∀ a, ι₂ (aκ a) = algebraMap F (RatFunc F) a) ∧
      (∀ a, resB B (νpt c a) ≠ 0) := by
  obtain ⟨ψ, hψ⟩ := exists_psi c n hV
  obtain ⟨B, hRB, hval⟩ := exists_valuationSubring_of_ringHom _ ψ
  have hνR : ∀ a, νpt c a ∈ (νsharp (F := F) c).toRingHom.range := fun a =>
    RingHom.mem_range.2 ⟨MvPolynomial.X a, νsharp_X c a⟩
  have hαR : ∀ a, algebraMap F (Lfield F r) a ∈ (νsharp (F := F) c).toRingHom.range := fun a =>
    RingHom.mem_range.2 ⟨MvPolynomial.C a, νsharp_C c a⟩
  have hψ' : ∀ (x : Lfield F r) (hx : x ∈ (νsharp (F := F) c).toRingHom.range)
      (f : MvPolynomial F F),
      νsharp c f = x → ψ ⟨x, hx⟩ = MvPolynomial.aeval (Pn n) f := by
    rintro x hx f rfl
    exact hψ f
  have hψν : ∀ a, ψ ⟨νpt c a, hνR a⟩ = Pn n a := fun a => by
    rw [hψ' _ _ (MvPolynomial.X a) (νsharp_X c a), MvPolynomial.aeval_X]
  have hψα : ∀ a, ψ ⟨algebraMap F (Lfield F r) a, hαR a⟩ = algebraMap F (RatFunc F) a :=
    fun a => by rw [hψ' _ _ (MvPolynomial.C a) (νsharp_C c a), MvPolynomial.aeval_C]
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : (νsharp (F := F) c).toRingHom.range →+* IsLocalRing.ResidueField B,
      φ₁ = (IsLocalRing.residue B).comp (Subring.inclusion hRB) := ⟨_, rfl⟩
  have hφ₁' : ∀ x : (νsharp (F := F) c).toRingHom.range, φ₁ x = resB B x := fun x => by
    rw [hφ₁, RingHom.comp_apply, resB_of_mem B (hRB x.2)]
    rfl
  have hker : ∀ x, φ₁ x = 0 ↔ ψ x = 0 := fun x => by
    rw [hφ₁', resB_eq_zero_iff B (hRB x.2)]
    exact hval x x.2
  obtain ⟨κ, _, θ, ι₁, ι₂, hι₁inj, hι₂inj, hι₁, hι₂⟩ := exists_common_field φ₁ ψ hker
  refine ⟨B, κ, inferInstance, ι₁, ι₂, fun a => θ ⟨νpt c a, hνR a⟩,
    fun a => θ ⟨algebraMap F (Lfield F r) a, hαR a⟩, hι₁inj, hι₂inj, fun a => hRB (hνR a),
    fun a => hRB (hαR a), ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [← RingHom.comp_apply, hι₁, hφ₁']
  · intro a
    rw [← RingHom.comp_apply, hι₂, hψν]
  · intro a
    rw [← RingHom.comp_apply, hι₁, hφ₁']
  · intro a
    rw [← RingHom.comp_apply, hι₂, hψα]
  · intro a
    rw [Ne, resB_eq_zero_iff B (hRB (hνR a)), hval _ (hνR a), hψν]
    exact zpow_ne_zero _ (algebraMap_X_add_C_ne_zero a)

/-! ### The main theorem -/

set_option maxHeartbeats 1600000 in
/-- **Backward direction of (2.x) in Proposition 2.6.** If `P^n` lies on the closure of the image
of `ν` (every `f ∈ I` vanishes at `P^n`) and `ζ^n = ζ^{∑ᵢ cᵢ}` for a generator `ζ` of `Fˣ`, then
`n ∈ E_q(c)`. -/
theorem mem_Eset_of_aeval_Pn_eq_zero (p e : ℕ) [Fact p.Prime] [CharP F p]
    (hq : Fintype.card F = p ^ e) (he : 1 ≤ e) (hr : 1 ≤ r) (hc : ∀ i, c i ≠ 0)
    (hC : 4 * ∑ i, (c i).natAbs < p ^ e) {ζ : F} (hζ : orderOf ζ = p ^ e - 1) (n : ℤ)
    (hV : ∀ f ∈ torusIdeal (F := F) c, MvPolynomial.aeval (Pn n) f = 0)
    (hζn : ζ ^ n = ζ ^ (∑ i, c i)) :
    n ∈ Eset (p ^ e) c := by
  classical
  have _hr := hr
  -- numerics
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq2 : 2 ≤ p ^ e := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  have hpe : 2 * p ^ (e - 1) ≤ p ^ e := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ']
    exact Nat.mul_le_mul_right _ hp2
  have hrC : r ≤ ∑ i, (c i).natAbs := by
    calc r = ∑ _i : Fin r, 1 := by simp
      _ ≤ ∑ i, (c i).natAbs :=
        Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 (hc i))
  -- the valuation point
  obtain ⟨B, κ, _, ι₁, ι₂, τκ, aκ, hι₁inj, hι₂inj, hνB, hαB, hι₁τ, hι₂τ, hι₁a, hι₂a, hν0⟩ :=
    exists_valuation_point_data c n hV
  -- the coordinates `yᵢ ∈ L`
  obtain ⟨yL, hyL⟩ : ∃ yL : Fin r → Lfield F r, yL = fun i =>
      algebraMap (MvPolynomial (Fin r) F) (Lfield F r) (MvPolynomial.X i) := ⟨_, rfl⟩
  have hlin : ∀ (i : Fin r) (a : F), algebraMap (MvPolynomial (Fin r) F) (Lfield F r)
      (MvPolynomial.X i + MvPolynomial.C a) = yL i + algebraMap F (Lfield F r) a := by
    intro i a
    rw [hyL, map_add, IsScalarTower.algebraMap_apply F (MvPolynomial (Fin r) F) (Lfield F r),
      MvPolynomial.algebraMap_eq]
  have hy0 : ∀ i, yL i ≠ 0 := fun i => by
    have h := algebraMap_mvX_add_C_ne_zero (F := F) i 0
    rwa [hlin, map_zero, add_zero] at h
  have hya : ∀ (a : F) (i : Fin r), yL i + algebraMap F (Lfield F r) a ≠ 0 := fun a i => by
    rw [← hlin]
    exact algebraMap_mvX_add_C_ne_zero i a
  have hνeq : ∀ a : F, νpt c a = ∏ i, (yL i + algebraMap F (Lfield F r) a) ^ c i := fun a => by
    unfold νpt
    exact Finset.prod_congr rfl fun i _ => by rw [hlin]
  -- the index set `S` and a base point `b₀`
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin r), S = Sfin B yL := ⟨_, rfl⟩
  have hScard : S.card ≤ r := by
    rw [hS]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hainj : Function.Injective (fun a : F => resB B (algebraMap F (Lfield F r) a)) := by
    intro a b hab
    have hab' : resB B (algebraMap F (Lfield F r) a) = resB B (algebraMap F (Lfield F r) b) := hab
    rw [← hι₁a, ← hι₁a] at hab'
    have h2 := congrArg ι₂ (hι₁inj hab')
    rw [hι₂a, hι₂a] at h2
    exact (algebraMap F (RatFunc F)).injective h2
  obtain ⟨b₀, hb₀⟩ := exists_good_base S (fun a : F => resB B (algebraMap F (Lfield F r) a)) hainj
    (fun i => resB B (yL i)) (by rw [hq]; omega)
  have hFnum : Fnum B yL c (resB B (algebraMap F (Lfield F r) b₀)) ≠ 0 := by
    unfold Fnum
    exact Finset.prod_ne_zero_iff.2 fun i hi =>
      pow_ne_zero _ (hb₀ i (by rw [hS]; exact (Finset.mem_filter.1 hi).1))
  have hFden : Fden B yL c (resB B (algebraMap F (Lfield F r) b₀)) ≠ 0 := by
    unfold Fden
    exact Finset.prod_ne_zero_iff.2 fun i hi =>
      pow_ne_zero _ (hb₀ i (by rw [hS]; exact (Finset.mem_filter.1 hi).1))
  -- the polynomials `N`, `D` over `κ(B)`
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = resB B (νpt c b₀) *
      Fden B yL c (resB B (algebraMap F (Lfield F r) b₀)) := ⟨_, rfl⟩
  obtain ⟨d₀, hd₀⟩ : ∃ d₀, d₀ = Fnum B yL c (resB B (algebraMap F (Lfield F r) b₀)) := ⟨_, rfl⟩
  have hn₀0 : n₀ ≠ 0 := by rw [hn₀]; exact mul_ne_zero (hν0 b₀) hFden
  have hd₀0 : d₀ ≠ 0 := by rw [hd₀]; exact hFnum
  obtain ⟨N, hN⟩ : ∃ N, N = Npoly B yL c n₀ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = Dpoly B yL c d₀ := ⟨_, rfl⟩
  have hD0 : D ≠ 0 := by rw [hD]; exact Dpoly_ne_zero B yL c hd₀0
  have hdegND : N.natDegree + D.natDegree ≤ ∑ i, (c i).natAbs := by
    rw [hN, hD]
    exact (add_le_add (natDegree_Npoly_le B yL c n₀) (natDegree_Dpoly_le B yL c d₀)).trans
      (sum_toNat_add_sum_toNat_neg_le _ c)
  -- the relation `N(ā) = ν̄_a D(ā)` over `κ(B)`, and coefficient descent to `κ`
  letI : Algebra κ (IsLocalRing.ResidueField B) := ι₁.toAlgebra
  have hrel : ∀ a ∈ (Finset.univ : Finset F),
      N.eval (algebraMap κ (IsLocalRing.ResidueField B) (aκ a)) =
        algebraMap κ (IsLocalRing.ResidueField B) (τκ a) *
          D.eval (algebraMap κ (IsLocalRing.ResidueField B) (aκ a)) := by
    intro a _
    rw [RingHom.algebraMap_toAlgebra, hι₁a, hι₁τ, hN, hD, hn₀, hd₀, hνeq a, hνeq b₀]
    exact Npoly_eval_eq B yL c hy0 (hαB a) (hαB b₀) (hya a) (hya b₀)
      (by rw [← hνeq]; exact hνB a) (by rw [← hνeq]; exact hνB b₀)
  obtain ⟨N₀, D₀, hD₀, hdegN₀, hdegD₀, hrel₀⟩ :=
    exists_coeff_descent N D hD0 Finset.univ aκ τκ hrel
  have haκinj : Set.InjOn aκ ↑(Finset.univ : Finset F) := by
    intro a _ b _ hab
    have h2 := congrArg ι₂ hab
    rw [hι₂a, hι₂a] at h2
    exact (algebraMap F (RatFunc F)).injective h2
  have hcard : N.natDegree + D.natDegree < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, hq]
    omega
  have hND := coeff_descent_eq N D N₀ D₀ Finset.univ aκ τκ haκinj hcard hdegN₀ hdegD₀ hrel hrel₀
  -- over `K = F(t)`: clearing denominators
  have hrelK : ∀ a ∈ (Finset.univ : Finset F),
      (N₀.map ι₂).eval (algebraMap F (RatFunc F) a) =
        Pn n a * (D₀.map ι₂).eval (algebraMap F (RatFunc F) a) := by
    intro a _
    rw [Polynomial.eval_map, Polynomial.eval_map, ← hι₂a a, Polynomial.eval₂_at_apply,
      Polynomial.eval₂_at_apply, hrel₀ a (Finset.mem_univ a), map_mul, hι₂τ a]
  have hD₀K : D₀.map ι₂ ≠ 0 := (Polynomial.map_ne_zero_iff hι₂inj).2 hD₀
  obtain ⟨N₂, D₂, β, hβ, hN₂, hD₂, hD₂0, hdegN₂, hdegD₂, hrel₂⟩ :=
    exists_clear_pair (N₀.map ι₂) (D₀.map ι₂) hD₀K n Finset.univ hrelK
  -- the reconstruction lemma
  have hcard₂ : p ^ (e - 1) + N₂.natDegree + D₂.natDegree < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, hq, hdegN₂, hdegD₂, natDegree_map_eq_of_injective hι₂inj,
      natDegree_map_eq_of_injective hι₂inj]
    omega
  obtain ⟨Lr, d, -, hsum, hprod⟩ :=
    reconstruct p e (K := RatFunc F) hq he n N₂ D₂ Finset.univ hD₂0 hcard₂ hrel₂
  -- the compositum `Ω` and the identity between the two descriptions of `N/D`
  obtain ⟨Ω, _, j₁, j₂, hj⟩ := exists_compositum ι₁ ι₂
  have hT3 := transport_reconstruct j₂ N₂ D₂ (N₀.map ι₂) (D₀.map ι₂) β hβ hN₂ hD₂ (p ^ e) Lr d
    hprod
  have hT1 := transport_descent ι₁ j₁ N D N₀ D₀ hD0 hD₀ hND
  have hT2 := map_Npoly_div_map_Dpoly B yL c j₁ n₀ d₀
  have hz : Set.InjOn (fun ℓ : ℕ => j₂ (algebraMap (Polynomial F) (RatFunc F)
      (Polynomial.X ^ (p ^ e) ^ ℓ))) ↑(Finset.range Lr) := by
    intro ℓ₁ _ ℓ₂ _ h
    have h' : j₂ (algebraMap (Polynomial F) (RatFunc F) (Polynomial.X ^ (p ^ e) ^ ℓ₁)) =
        j₂ (algebraMap (Polynomial F) (RatFunc F) (Polynomial.X ^ (p ^ e) ^ ℓ₂)) := h
    have h1 := (IsFractionRing.injective (Polynomial F) (RatFunc F)) (j₂.injective h')
    have h2 := congrArg Polynomial.natDegree h1
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at h2
    exact Nat.pow_right_injective hq2 h2
  obtain ⟨κ', hκ'⟩ : ∃ κ' : Ω, κ' = j₁ n₀ / j₁ d₀ := ⟨_, rfl⟩
  have hκ'0 : κ' ≠ 0 := by
    rw [hκ']
    exact div_ne_zero ((map_ne_zero j₁).2 hn₀0) ((map_ne_zero j₁).2 hd₀0)
  have hid : algebraMap (Polynomial Ω) (RatFunc Ω) (C κ') *
      ∏ i ∈ S, algebraMap (Polynomial Ω) (RatFunc Ω) (X + C (j₁ (resB B (yL i)))) ^ c i =
      ∏ ℓ ∈ Finset.range Lr, algebraMap (Polynomial Ω) (RatFunc Ω)
        (X + C (j₂ (algebraMap (Polynomial F) (RatFunc F) (Polynomial.X ^ (p ^ e) ^ ℓ)))) ^ d ℓ := by
    rw [hκ', hS, ← hT2, ← hN, ← hD, ← hT1, ← hT3, Polynomial.map_map, Polynomial.map_map, hj]
  -- grouping the exponents
  have hgroup := group_weights S (fun i => j₁ (resB B (yL i))) c Lr
    (fun ℓ : ℕ => j₂ (algebraMap (Polynomial F) (RatFunc F) (Polynomial.X ^ (p ^ e) ^ ℓ))) hz d κ'
    hκ'0 hid
  obtain ⟨kk, hkk⟩ := exists_exponents S _ c Lr _ hz d hgroup ((p ^ e : ℕ) : ℤ)
  obtain ⟨kk1, hkk1⟩ := exists_exponents S _ c Lr _ hz d hgroup 1
  simp only [one_pow, mul_one] at hkk1
  -- the congruence and the final arithmetic
  have hmod : n ≡ ∑ i, c i [ZMOD ((p ^ e - 1 : ℕ) : ℤ)] := modEq_of_zpow_eq (by omega) hζ hζn
  exact final_arith c (p ^ e) hq2 n S Lr d hsum kk hkk hkk1 hmod (by omega)

end Main

end ArithDyn.Derksen
