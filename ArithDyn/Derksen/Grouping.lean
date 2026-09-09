import Mathlib

/-!
# Grouping the exponents of a rational function written in two ways

Over a field `Ω`, suppose the same rational function is written in two ways as a product of
linear factors with integer exponents,
`κ · ∏_{i ∈ S} (X + y_i)^{c_i} = ∏_{ℓ < L} (X + z_ℓ)^{d_ℓ}` in `Ω(X)`,
with `κ ≠ 0` and the `z_ℓ` pairwise distinct.

* `group_weights`: comparing the multiplicity of the root `-w` on both sides gives, for every
  `w ∈ Ω`, `∑_{i ∈ S, y_i = w} c_i = ∑_{ℓ < L, z_ℓ = w} d_ℓ`. We clear denominators (writing each
  `zpow` as a quotient of natural powers), obtain a polynomial identity in `Ω[X]`, and compare
  `Polynomial.rootMultiplicity (-w)` of both sides.
* `exists_exponents`: consequently, for every integer `q` there are exponents `kk_i`
  (`kk_i = ℓ` if `y_i = z_ℓ`, else `0`) with `∑_{i ∈ S} c_i q^{kk_i} = ∑_{ℓ < L} d_ℓ q^ℓ`
  (group both sums by the value in `Ω`).
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

open Polynomial

/-! ### Auxiliary lemmas: `zpow` as a quotient, nonvanishing of linear factors -/

/-- `x ^ n = x ^ n.toNat / x ^ (-n).toNat` for `x ≠ 0` in a field. -/
theorem zpow_eq_pow_toNat_div_pow_toNat_neg {K : Type*} [Field K] {x : K} (hx : x ≠ 0) (n : ℤ) :
    x ^ n = x ^ n.toNat / x ^ (-n).toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hx, Int.toNat_sub_toNat_neg]

theorem prod_linear_pow_ne_zero {R : Type*} [CommRing R] [IsDomain R] {α : Type*} (T : Finset α)
    (g : α → R) (n : α → ℕ) : ∏ a ∈ T, (X + C (g a)) ^ n a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ (X_add_C_ne_zero _)

theorem algebraMap_linear_ne_zero {Ω : Type*} [Field Ω] (b : Ω) :
    algebraMap (Polynomial Ω) (RatFunc Ω) (X + C b) ≠ 0 := fun h =>
  X_add_C_ne_zero b (IsFractionRing.to_map_eq_zero_iff.1 h)

theorem algebraMap_prod_linear_pow_ne_zero {Ω : Type*} [Field Ω] {α : Type*} (T : Finset α)
    (g : α → Ω) (n : α → ℕ) :
    algebraMap (Polynomial Ω) (RatFunc Ω) (∏ a ∈ T, (X + C (g a)) ^ n a) ≠ 0 := fun h =>
  prod_linear_pow_ne_zero T g n (IsFractionRing.to_map_eq_zero_iff.1 h)

/-- A product of `zpow`s of linear factors in `Ω(X)` as a quotient of two polynomials. -/
theorem prod_algebraMap_linear_zpow {Ω : Type*} [Field Ω] {α : Type*} (T : Finset α) (g : α → Ω)
    (n : α → ℤ) :
    ∏ a ∈ T, (algebraMap (Polynomial Ω) (RatFunc Ω) (X + C (g a))) ^ n a =
      algebraMap (Polynomial Ω) (RatFunc Ω) (∏ a ∈ T, (X + C (g a)) ^ (n a).toNat) /
        algebraMap (Polynomial Ω) (RatFunc Ω) (∏ a ∈ T, (X + C (g a)) ^ (-(n a)).toNat) := by
  rw [map_prod, map_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_pow, map_pow]
  exact zpow_eq_pow_toNat_div_pow_toNat_neg (algebraMap_linear_ne_zero (g a)) (n a)

/-! ### Auxiliary lemmas: root multiplicities of products of linear factors -/

theorem rootMultiplicity_finset_prod {R : Type*} [CommRing R] [IsDomain R] {α : Type*}
    (T : Finset α) (f : α → R[X]) (hf : ∀ a ∈ T, f a ≠ 0) (x : R) :
    rootMultiplicity x (∏ a ∈ T, f a) = ∑ a ∈ T, rootMultiplicity x (f a) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, ← C_1, rootMultiplicity_C]
  | insert a T ha ih =>
    have hT : ∀ b ∈ T, f b ≠ 0 := fun b hb => hf b (Finset.mem_insert_of_mem hb)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      rootMultiplicity_mul (mul_ne_zero (hf a (Finset.mem_insert_self a T))
        (Finset.prod_ne_zero_iff.2 hT)), ih hT]

theorem rootMultiplicity_neg_X_add_C_pow {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (w b : R) (n : ℕ) :
    rootMultiplicity (-w) ((X + C b) ^ n) = if b = w then n else 0 := by
  split_ifs with h
  · subst h
    rw [show (X + C b : R[X]) = X - C (-b) by rw [C_neg, sub_neg_eq_add],
      rootMultiplicity_X_sub_C_pow]
  · apply rootMultiplicity_eq_zero
    rw [IsRoot.def, eval_pow, eval_add, eval_X, eval_C]
    exact pow_ne_zero _ fun h0 => h (by linear_combination h0)

theorem rootMultiplicity_prod_linear_pow {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    {α : Type*} (T : Finset α) (g : α → R) (n : α → ℕ) (w : R) :
    rootMultiplicity (-w) (∏ a ∈ T, (X + C (g a)) ^ n a) =
      ∑ a ∈ T.filter (fun a => g a = w), n a := by
  rw [rootMultiplicity_finset_prod T (fun a => (X + C (g a)) ^ n a)
    (fun a _ => pow_ne_zero _ (X_add_C_ne_zero _)), Finset.sum_filter]
  exact Finset.sum_congr rfl fun a _ => rootMultiplicity_neg_X_add_C_pow w (g a) (n a)

/-! ### The two main statements -/

-- The injectivity hypothesis `hz` is part of the fixed interface but is not needed for the
-- multiplicity comparison itself (it is used in `exists_exponents`).
set_option linter.unusedVariables false in
open scoped Classical in
/-- Multiplicity comparison for a rational function written in two ways as a product of linear
factors with integer exponents. -/
theorem group_weights {Ω : Type*} [Field Ω] {ι : Type*} (S : Finset ι) (y : ι → Ω) (c : ι → ℤ)
    (L : ℕ) (z : ℕ → Ω) (hz : Set.InjOn z ↑(Finset.range L)) (d : ℕ → ℤ) (κ : Ω) (hκ : κ ≠ 0)
    (hid : algebraMap (Polynomial Ω) (RatFunc Ω) (C κ) *
        ∏ i ∈ S, (algebraMap (Polynomial Ω) (RatFunc Ω) (X + C (y i))) ^ c i =
      ∏ ℓ ∈ Finset.range L, (algebraMap (Polynomial Ω) (RatFunc Ω) (X + C (z ℓ))) ^ d ℓ) :
    ∀ w : Ω, ∑ i ∈ S.filter (fun i => y i = w), c i =
      ∑ ℓ ∈ (Finset.range L).filter (fun ℓ => z ℓ = w), d ℓ := by
  intro w
  have hφinj : Function.Injective (algebraMap (Polynomial Ω) (RatFunc Ω)) :=
    IsFractionRing.injective (Polynomial Ω) (RatFunc Ω)
  -- the four polynomials obtained by separating positive and negative exponents
  have hA : (∏ i ∈ S, (X + C (y i)) ^ (c i).toNat : Polynomial Ω) ≠ 0 :=
    prod_linear_pow_ne_zero _ _ _
  have hA' : (∏ i ∈ S, (X + C (y i)) ^ (-(c i)).toNat : Polynomial Ω) ≠ 0 :=
    prod_linear_pow_ne_zero _ _ _
  have hB : (∏ ℓ ∈ Finset.range L, (X + C (z ℓ)) ^ (d ℓ).toNat : Polynomial Ω) ≠ 0 :=
    prod_linear_pow_ne_zero _ _ _
  have hB' : (∏ ℓ ∈ Finset.range L, (X + C (z ℓ)) ^ (-(d ℓ)).toNat : Polynomial Ω) ≠ 0 :=
    prod_linear_pow_ne_zero _ _ _
  -- clear denominators: a polynomial identity in `Ω[X]`
  rw [prod_algebraMap_linear_zpow, prod_algebraMap_linear_zpow, mul_div_assoc',
    div_eq_div_iff (algebraMap_prod_linear_pow_ne_zero _ _ _)
      (algebraMap_prod_linear_pow_ne_zero _ _ _)] at hid
  have hpoly : C κ * (∏ i ∈ S, (X + C (y i)) ^ (c i).toNat) *
        ∏ ℓ ∈ Finset.range L, (X + C (z ℓ)) ^ (-(d ℓ)).toNat =
      (∏ ℓ ∈ Finset.range L, (X + C (z ℓ)) ^ (d ℓ).toNat) *
        ∏ i ∈ S, (X + C (y i)) ^ (-(c i)).toNat :=
    hφinj (by rw [map_mul, map_mul, map_mul]; exact hid)
  -- compare the multiplicities of the root `-w`
  have hm := congrArg (rootMultiplicity (-w)) hpoly
  rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (C_ne_zero.2 hκ) hA) hB'),
    rootMultiplicity_mul (mul_ne_zero (C_ne_zero.2 hκ) hA), rootMultiplicity_mul (mul_ne_zero hB hA'),
    rootMultiplicity_C, zero_add, rootMultiplicity_prod_linear_pow,
    rootMultiplicity_prod_linear_pow, rootMultiplicity_prod_linear_pow,
    rootMultiplicity_prod_linear_pow] at hm
  have hm' := congrArg (Nat.cast (R := ℤ)) hm
  push_cast at hm'
  -- back to integer exponents
  have hc : ∀ i ∈ S.filter (fun i => y i = w),
      c i = ((c i).toNat : ℤ) - ((-(c i)).toNat : ℤ) :=
    fun i _ => (Int.toNat_sub_toNat_neg _).symm
  have hd : ∀ ℓ ∈ (Finset.range L).filter (fun ℓ => z ℓ = w),
      d ℓ = ((d ℓ).toNat : ℤ) - ((-(d ℓ)).toNat : ℤ) :=
    fun ℓ _ => (Int.toNat_sub_toNat_neg _).symm
  rw [Finset.sum_congr rfl hc, Finset.sum_congr rfl hd, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  linarith

open scoped Classical in
/-- Regrouping the exponents. -/
theorem exists_exponents {Ω : Type*} [Field Ω] {ι : Type*} [DecidableEq ι] (S : Finset ι) (y : ι → Ω)
    (c : ι → ℤ) (L : ℕ) (z : ℕ → Ω) (hz : Set.InjOn z ↑(Finset.range L)) (d : ℕ → ℤ)
    (hgroup : ∀ w : Ω, ∑ i ∈ S.filter (fun i => y i = w), c i =
      ∑ ℓ ∈ (Finset.range L).filter (fun ℓ => z ℓ = w), d ℓ) (q : ℤ) :
    ∃ kk : ι → ℕ, ∑ i ∈ S, c i * q ^ kk i = ∑ ℓ ∈ Finset.range L, d ℓ * q ^ ℓ := by
  -- the exponent attached to a value `w ∈ Ω`: the index `ℓ < L` with `z ℓ = w`, if any
  obtain ⟨e, he⟩ : ∃ e : Ω → ℕ, ∀ ℓ, ℓ < L → e (z ℓ) = ℓ := by
    refine ⟨fun w => if h : ∃ ℓ, ℓ < L ∧ z ℓ = w then Classical.choose h else 0,
      fun ℓ hℓ => ?_⟩
    have h : ∃ ℓ', ℓ' < L ∧ z ℓ' = z ℓ := ⟨ℓ, hℓ, rfl⟩
    have hspec := Classical.choose_spec h
    dsimp only
    rw [dif_pos h]
    exact hz (Finset.mem_coe.2 (Finset.mem_range.2 hspec.1))
      (Finset.mem_coe.2 (Finset.mem_range.2 hℓ)) hspec.2
  refine ⟨fun i => e (y i), ?_⟩
  -- fiberwise comparison: on the fiber over `w`, the exponent is constant
  have key : ∀ w : Ω, ∑ i ∈ S.filter (fun i => y i = w), c i * q ^ e (y i) =
      ∑ ℓ ∈ (Finset.range L).filter (fun ℓ => z ℓ = w), d ℓ * q ^ ℓ := by
    intro w
    calc ∑ i ∈ S.filter (fun i => y i = w), c i * q ^ e (y i)
        = ∑ i ∈ S.filter (fun i => y i = w), c i * q ^ e w := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [(Finset.mem_filter.1 hi).2]
      _ = (∑ i ∈ S.filter (fun i => y i = w), c i) * q ^ e w := by rw [Finset.sum_mul]
      _ = (∑ ℓ ∈ (Finset.range L).filter (fun ℓ => z ℓ = w), d ℓ) * q ^ e w := by
          rw [hgroup w]
      _ = ∑ ℓ ∈ (Finset.range L).filter (fun ℓ => z ℓ = w), d ℓ * q ^ e w := by
          rw [Finset.sum_mul]
      _ = ∑ ℓ ∈ (Finset.range L).filter (fun ℓ => z ℓ = w), d ℓ * q ^ ℓ := by
          refine Finset.sum_congr rfl fun ℓ hℓ => ?_
          obtain ⟨hℓL, hℓw⟩ := Finset.mem_filter.1 hℓ
          rw [← hℓw, he ℓ (Finset.mem_range.1 hℓL)]
  -- group both sides by the value in `Ω`
  have hy : ∀ i ∈ S, y i ∈ S.image y ∪ (Finset.range L).image z := fun i hi =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem y hi)
  have hzt : ∀ ℓ ∈ Finset.range L, z ℓ ∈ S.image y ∪ (Finset.range L).image z := fun ℓ hℓ =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem z hℓ)
  rw [← Finset.sum_fiberwise_of_maps_to hy, ← Finset.sum_fiberwise_of_maps_to hzt]
  exact Finset.sum_congr rfl fun w _ => key w

end ArithDyn.Derksen
