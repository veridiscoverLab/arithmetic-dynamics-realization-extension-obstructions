import ArithDyn.Derksen.Descent

/-!
# Rational function fields: Galois descent and intersections (paper §2.2, Lemmas 2.3–2.4)

The paper works over `𝔽_q(t)` and `𝔽_p(t)`. A finite Galois extension `L/F` induces the
extension of rational function fields `L(t)/F(t)`, via the ring hom `ratFuncMap : F(t) → L(t)`.

* `RClass.descent_ratFunc`: `L(t)/F(t)` is finite Galois, so Lemma 2.4 (`RClass.descent`)
  gives `𝓡_{L(t)} ⊆ 𝓡_{F(t)}`. We exhibit `L(t)` as the splitting field over `F(t)` of the
  minimal polynomial of a primitive element of `L/F`.
* `eq_zero_of_sum_ratFuncMap_mul_eq_zero`: `F`-linearly independent elements of `L` remain
  `F(t)`-linearly independent in `L(t)` (clear denominators and compare coefficients).
* `RClass.inter_mem_ratFunc`, `RClass.finset_iInter_mem_ratFunc`: over a finite field `F`,
  `𝓡_{F(t)}` is closed under finite intersections. Taking a Galois extension `E/F` with
  `1, β` linearly independent, the zero set of `u + β v` over `E(t)` is `Z(u) ∩ Z(v)`, and
  descent brings it back to `F(t)`.
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

open Polynomial
open scoped nonZeroDivisors IntermediateField

universe u v

variable {F : Type u} {L : Type v} [Field F] [Field L] [Algebra F L]

/-! ### The ring hom `F(t) → L(t)` -/

theorem polynomialMap_le_comap :
    (Polynomial F)⁰ ≤ (Polynomial L)⁰.comap (Polynomial.mapRingHom (algebraMap F L)) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (by rw [Polynomial.coe_mapRingHom]; exact Polynomial.map_injective _ (algebraMap F L).injective)

/-- The ring hom `F(t) → L(t)` induced by `F → L`. -/
noncomputable def ratFuncMap : RatFunc F →+* RatFunc L :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap F L)) polynomialMap_le_comap

theorem ratFuncMap_algebraMap_polynomial (P : Polynomial F) :
    ratFuncMap (algebraMap (Polynomial F) (RatFunc F) P) =
      algebraMap (Polynomial L) (RatFunc L) (P.map (algebraMap F L)) := by
  have h := RatFunc.map_apply_div (Polynomial.mapRingHom (algebraMap F L))
    (polynomialMap_le_comap (F := F) (L := L)) P 1
  simp only [map_one, div_one] at h
  unfold ratFuncMap
  rw [RatFunc.coe_mapRingHom_eq_coe_map, h, Polynomial.coe_mapRingHom]

theorem ratFuncMap_algebraMap (a : F) :
    ratFuncMap (algebraMap F (RatFunc F) a) = algebraMap L (RatFunc L) (algebraMap F L a) := by
  rw [RatFunc.algebraMap_eq_C, RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C,
    ratFuncMap_algebraMap_polynomial, Polynomial.map_C, RatFunc.algebraMap_C]

theorem ratFuncMap_X : ratFuncMap (RatFunc.X : RatFunc F) = (RatFunc.X : RatFunc L) := by
  rw [← RatFunc.algebraMap_X, ratFuncMap_algebraMap_polynomial, Polynomial.map_X,
    RatFunc.algebraMap_X]

/-! ### Linear independence is preserved -/

/-- `F`-linearly independent elements of `L` are `F(t)`-linearly independent in `L(t)`. -/
theorem eq_zero_of_sum_ratFuncMap_mul_eq_zero {ι : Type*} (s : Finset ι) (β : ι → L)
    (hβ : LinearIndependent F β) (c : ι → RatFunc F)
    (h : ∑ i ∈ s, ratFuncMap (c i) * algebraMap L (RatFunc L) (β i) = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical
  -- clear denominators: `D • c i = N i` with `D ∈ F[X]` nonzero and `N i ∈ F[X]`
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples (Polynomial F)⁰ s c
  have hD' : ∀ i ∈ s, ∃ N : Polynomial F,
      algebraMap (Polynomial F) (RatFunc F) N = (D : Polynomial F) • c i :=
    fun i hi => RingHom.mem_rangeS.1 (hD i hi)
  choose! N hN using hD'
  have hDne : (D : Polynomial F) ≠ 0 := nonZeroDivisors.ne_zero D.2
  -- the polynomial identity `∑ᵢ (N i)(t) βᵢ = 0` in `L[X]`
  have hpoly : ∑ i ∈ s, (N i).map (algebraMap F L) * Polynomial.C (β i) = 0 := by
    apply IsFractionRing.injective (Polynomial L) (RatFunc L)
    rw [map_sum, map_zero]
    calc ∑ i ∈ s, algebraMap (Polynomial L) (RatFunc L)
          ((N i).map (algebraMap F L) * Polynomial.C (β i))
        = ∑ i ∈ s, ratFuncMap (algebraMap (Polynomial F) (RatFunc F) (D : Polynomial F)) *
            (ratFuncMap (c i) * algebraMap L (RatFunc L) (β i)) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [map_mul, ← ratFuncMap_algebraMap_polynomial, hN i hi, Algebra.smul_def, map_mul,
            RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, mul_assoc]
      _ = 0 := by rw [← Finset.mul_sum, h, mul_zero]
  -- compare coefficients and use linear independence
  have hcoeff : ∀ k : ℕ, ∀ i ∈ s, (N i).coeff k = 0 := by
    intro k
    have h1 := congrArg (fun P : Polynomial L => P.coeff k) hpoly
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_mul_C, Polynomial.coeff_map,
      Polynomial.coeff_zero] at h1
    refine linearIndependent_iff'.1 hβ s (fun i => (N i).coeff k) ?_
    simpa only [Algebra.smul_def] using h1
  intro i hi
  have hNi : N i = 0 := Polynomial.ext (fun k => by rw [hcoeff k i hi, Polynomial.coeff_zero])
  have h2 := hN i hi
  rw [hNi, map_zero, Algebra.smul_def] at h2
  rcases mul_eq_zero.1 h2.symm with h0 | h0
  · exact absurd ((map_eq_zero_iff _ (IsFractionRing.injective (Polynomial F) (RatFunc F))).1 h0)
      hDne
  · exact h0

/-! ### `L(t)/F(t)` is finite Galois; descent -/

/-- Galois descent for rational function fields: `𝓡_{L(t)} ⊆ 𝓡_{F(t)}` for `L/F` finite
Galois. -/
theorem RClass.descent_ratFunc [FiniteDimensional F L] [IsGalois F L] {B : Set ℤ}
    (hB : B ∈ RClass (RatFunc L)) : B ∈ RClass (RatFunc F) := by
  classical
  letI : Algebra (RatFunc F) (RatFunc L) := (ratFuncMap (F := F) (L := L)).toAlgebra
  have hcomp : (algebraMap (RatFunc F) (RatFunc L)).comp (algebraMap F (RatFunc F)) =
      (algebraMap L (RatFunc L)).comp (algebraMap F L) :=
    RingHom.ext (fun a => ratFuncMap_algebraMap a)
  have hnormal : Normal F L := inferInstance
  -- a primitive element `α` of `L/F` and its minimal polynomial `m'` viewed over `F(t)`
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F L
  have hint : IsIntegral F α := IsIntegral.of_finite F α
  obtain ⟨m', hm'⟩ : ∃ m' : Polynomial (RatFunc F),
      m' = (minpoly F α).map (algebraMap F (RatFunc F)) := ⟨_, rfl⟩
  have hm'ne : m' ≠ 0 := by
    rw [hm']
    exact (Polynomial.map_ne_zero_iff (algebraMap F (RatFunc F)).injective).2
      (minpoly.ne_zero hint)
  have hm'monic : m'.Monic := by rw [hm']; exact (minpoly.monic hint).map _
  have hm'sep : m'.Separable := by
    rw [hm']
    exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F α)
  have haeval : Polynomial.aeval (algebraMap L (RatFunc L) α) m' = 0 := by
    rw [Polynomial.aeval_def, hm', Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have hint' : IsIntegral (RatFunc F) (algebraMap L (RatFunc L) α) := ⟨m', hm'monic, haeval⟩
  have hroot : algebraMap L (RatFunc L) α ∈ m'.rootSet (RatFunc L) := by
    rw [Polynomial.mem_rootSet']
    exact ⟨(Polynomial.map_ne_zero_iff (algebraMap (RatFunc F) (RatFunc L)).injective).2 hm'ne,
      haeval⟩
  -- `m'` splits in `L(t)` since `m` splits in `L`
  have hsplits : Polynomial.Splits (m'.map (algebraMap (RatFunc F) (RatFunc L))) := by
    rw [hm', Polynomial.map_map, hcomp, ← Polynomial.map_map]
    exact (hnormal.splits α).map _
  -- every element of `L(t)` lies in `F(t)(α)`
  have hK : ∀ x : RatFunc L, x ∈ (RatFunc F)⟮algebraMap L (RatFunc L) α⟯ := by
    have hpoly : ∀ P : Polynomial L,
        algebraMap (Polynomial L) (RatFunc L) P ∈ (RatFunc F)⟮algebraMap L (RatFunc L) α⟯ := by
      intro P
      induction P using Polynomial.induction_on' with
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | monomial n a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C,
          RatFunc.algebraMap_X]
        refine mul_mem ?_ (pow_mem ?_ n)
        · -- `a ∈ L = F[α]`, so `a = Q(α)` with `Q ∈ F[X]`
          have ha : a ∈ Algebra.adjoin F {α} := by
            rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
              IntermediateField.mem_toSubalgebra, hα]
            exact IntermediateField.mem_top
          rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
          obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).1 ha
          have hQ : (RatFunc.C : L →+* RatFunc L) (Polynomial.aeval α Q) =
              Polynomial.aeval (algebraMap L (RatFunc L) α)
                (Q.map (algebraMap F (RatFunc F))) := by
            simp only [Polynomial.aeval_def]
            rw [Polynomial.eval₂_map, hcomp, RatFunc.algebraMap_eq_C, Polynomial.hom_eval₂]
          rw [hQ, ← IntermediateField.mem_toSubalgebra,
            IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint'.isAlgebraic]
          exact Polynomial.aeval_mem_adjoin_singleton _ _
        · rw [← ratFuncMap_X (F := F) (L := L)]
          exact IntermediateField.algebraMap_mem _ _
    intro x
    rw [← RatFunc.num_div_denom x]
    exact IntermediateField.div_mem _ (hpoly _) (hpoly _)
  have hgen : Algebra.adjoin (RatFunc F) (m'.rootSet (RatFunc L)) = ⊤ := by
    rw [Algebra.eq_top_iff]
    intro x
    refine Algebra.adjoin_mono (Set.singleton_subset_iff.2 hroot) ?_
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint'.isAlgebraic,
      IntermediateField.mem_toSubalgebra]
    exact hK x
  haveI : Polynomial.IsSplittingField (RatFunc F) (RatFunc L) m' := ⟨hsplits, hgen⟩
  haveI : FiniteDimensional (RatFunc F) (RatFunc L) :=
    Polynomial.IsSplittingField.finiteDimensional (RatFunc L) m'
  haveI : IsGalois (RatFunc F) (RatFunc L) := IsGalois.of_separable_splitting_field hm'sep
  exact RClass.descent hB

/-! ### Intersections over a finite field -/

theorem IsFundRec.add {K : Type*} [Field K] {u v : ℤ → K} (hu : IsFundRec u) (hv : IsFundRec v) :
    IsFundRec (fun n => u n + v n) := by
  obtain ⟨ι, _, _, r, rfl⟩ := exists_rep_of_isFundRec hu
  obtain ⟨κ, _, _, s, rfl⟩ := exists_rep_of_isFundRec hv
  have := isFundRec_of_rep (r.add s)
  convert this using 1
  funext n
  rw [LinRepZ.add_seq]

variable (F) in
/-- A finite field `F` has a finite Galois extension `E` with an element `β` such that `1, β`
are `F`-linearly independent (the splitting field of `X^{q²} - X`, which has `q²` roots). -/
theorem exists_galois_linearIndependent_pair [Fintype F] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E)
      (β : E), LinearIndependent F ![1, β] := by
  classical
  obtain ⟨p, hp, n, -, hcard⟩ := FiniteField.card' F
  haveI : CharP F p := hp
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = Fintype.card F := ⟨_, rfl⟩
  have hq1 : 1 < q := by rw [hq]; exact Fintype.one_lt_card
  have hpq : p ∣ q ^ 2 := by
    rw [hq, hcard]
    exact (dvd_pow_self p n.ne_zero).trans (dvd_pow_self _ two_ne_zero)
  obtain ⟨f, hf⟩ : ∃ f : Polynomial F, f = X ^ (q ^ 2) - X := ⟨_, rfl⟩
  have hsep : f.Separable := by rw [hf]; exact galois_poly_separable p (q ^ 2) hpq
  have hdeg : f.natDegree = q ^ 2 := by
    rw [hf]; exact FiniteField.X_pow_card_sub_X_natDegree_eq F (one_lt_pow₀ hq1 two_ne_zero)
  -- the splitting field has at least `q²` elements
  have hcardroots : Nat.card (f.rootSet f.SplittingField) = q ^ 2 := by
    have h1 := Polynomial.card_rootSet_eq_natDegree hsep (Polynomial.SplittingField.splits f)
    rwa [← Nat.card_eq_fintype_card, hdeg] at h1
  have hle : q ^ 2 ≤ Nat.card f.SplittingField := by
    rw [← hcardroots]
    exact Nat.card_le_card_of_injective
      (Subtype.val : f.rootSet f.SplittingField → f.SplittingField) Subtype.val_injective
  have hnotsurj : ¬ Function.Surjective (algebraMap F f.SplittingField) := by
    intro hsurj
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    have h2 : Nat.card F = q := by rw [hq]; exact Nat.card_eq_fintype_card
    rw [h2] at h1
    nlinarith
  obtain ⟨β, hβ⟩ : ∃ β : f.SplittingField, ¬ ∃ a, algebraMap F f.SplittingField a = β :=
    not_forall.1 hnotsurj
  refine ⟨f.SplittingField, inferInstance, inferInstance, inferInstance, inferInstance, β, ?_⟩
  rw [LinearIndependent.pair_iff' (one_ne_zero : (1 : f.SplittingField) ≠ 0)]
  intro a ha
  exact hβ ⟨a, by rw [Algebra.algebraMap_eq_smul_one]; exact ha⟩

/-- Over a finite field, `𝓡` is closed under binary intersections. -/
theorem RClass.inter_mem_ratFunc [Fintype F] {B C : Set ℤ}
    (hB : B ∈ RClass (RatFunc F)) (hC : C ∈ RClass (RatFunc F)) : B ∩ C ∈ RClass (RatFunc F) := by
  obtain ⟨E, _, _, _, _, β, hβ⟩ := exists_galois_linearIndependent_pair F
  obtain ⟨u, hu, rfl⟩ := (mem_RClass_iff B).1 hB
  obtain ⟨v, hv, rfl⟩ := (mem_RClass_iff C).1 hC
  -- the zero set of `u + β v` over `E(t)` is `Z(u) ∩ Z(v)`
  refine RClass.descent_ratFunc (F := F) (L := E) ((mem_RClass_iff _).2
    ⟨fun n => ratFuncMap (u n) + ratFuncMap (v n) * algebraMap E (RatFunc E) β, ?_, ?_⟩)
  · exact (hu.map (ratFuncMap (F := F) (L := E))).add
      ((hv.map (ratFuncMap (F := F) (L := E))).mul (IsFundRec.const _))
  · ext n
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h
      have key := eq_zero_of_sum_ratFuncMap_mul_eq_zero (F := F) (L := E) Finset.univ ![1, β] hβ
        ![u n, v n] (by rw [Fin.sum_univ_two]; simpa using h)
      exact ⟨key 0 (Finset.mem_univ _), key 1 (Finset.mem_univ _)⟩
    · rintro ⟨h1, h2⟩
      simp [h1, h2]

/-- Over a finite field, `𝓡` is closed under finite intersections. -/
theorem RClass.finset_iInter_mem_ratFunc [Fintype F] {ι : Type*} (s : Finset ι) (S : ι → Set ℤ)
    (h : ∀ i ∈ s, S i ∈ RClass (RatFunc F)) : (⋂ i ∈ s, S i) ∈ RClass (RatFunc F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RClass.univ_mem (K := RatFunc F)
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    exact RClass.inter_mem_ratFunc (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end ArithDyn.Derksen
