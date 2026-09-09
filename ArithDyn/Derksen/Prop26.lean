import ArithDyn.Derksen.TorusBackward
import ArithDyn.Derksen.Decomposition

/-!
# Proposition 2.6 and Theorem 2.2 (paper §2.3–2.5)

Combining the forward direction (`aeval_Pn_eq_zero_of_mem_torusIdeal`), the backward direction
(`mem_Eset_of_aeval_Pn_eq_zero`), the recurrences `n ↦ f(P^n)` and `n ↦ ζ^n - ζ^{∑c}`, the closure
of `𝓡_{F(t)}` under finite intersections, and the Galois descent `𝓡_{𝔽_q(t)} ⊆ 𝓡_{𝔽_p(t)}`, we
obtain Proposition 2.6 (`prop26`), hence Proposition 2.7 and Theorem 2.2 unconditionally.
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-- **Proposition 2.6 over `F(t)`**: for `q = |F| = p^e > 4 ∑|cᵢ|`, `E_q(c) ∈ 𝓡_{F(t)}`. -/
theorem Eset_mem_RClass_ratFunc (p e : ℕ) [Fact p.Prime] [CharP F p]
    (hq : Fintype.card F = p ^ e) (he : 1 ≤ e) {r : ℕ} (c : Fin r → ℤ) (hr : 1 ≤ r)
    (hc : ∀ i, c i ≠ 0) (hC : 4 * ∑ i, (c i).natAbs < p ^ e) :
    Eset (p ^ e) c ∈ RClass (RatFunc F) := by
  classical
  obtain ⟨ζ, hζ0, hζ⟩ := exists_generator_orderOf F
  rw [hq] at hζ
  have hq2 : 2 ≤ p ^ e := le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow (by omega) p)
  have hcast : ((p ^ e - 1 : ℕ) : ℤ) = ((p ^ e : ℕ) : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  -- a finite generating set of the torus ideal
  obtain ⟨T, hT⟩ : (torusIdeal (F := F) c).FG := IsNoetherian.noetherian _
  -- the zero sets of the recurrences `n ↦ f(P^n)` and `n ↦ ζ^n - ζ^{∑c}`
  have hZ : ∀ f : MvPolynomial F F, {n : ℤ | MvPolynomial.aeval (Pn n) f = 0} ∈ RClass (RatFunc F) :=
    fun f => (mem_RClass_iff _).2 ⟨_, isFundRec_aeval_Pn f, rfl⟩
  have hζ0' : algebraMap F (RatFunc F) ζ ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hζ0
  have hZζ : {n : ℤ | (algebraMap F (RatFunc F) ζ) ^ n -
      (algebraMap F (RatFunc F) ζ) ^ (∑ i, c i) = 0} ∈ RClass (RatFunc F) :=
    (mem_RClass_iff _).2 ⟨_, isFundRec_zpow_sub hζ0' _, rfl⟩
  have hmem := RClass.inter_mem_ratFunc
    (RClass.finset_iInter_mem_ratFunc T (fun f => {n : ℤ | MvPolynomial.aeval (Pn n) f = 0})
      (fun f _ => hZ f)) hZζ
  convert hmem using 1
  ext n
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨fun f hf => ?_, ?_⟩
    · have := aeval_Pn_eq_zero_of_mem_torusIdeal c k (f := f) (hT ▸ Ideal.subset_span hf)
      rwa [hq] at this
    · rw [sub_eq_zero, ← map_zpow₀, ← map_zpow₀]
      congr 1
      have hu : (Units.mk0 ζ hζ0) ^ (∑ i, c i * ((p ^ e : ℕ) : ℤ) ^ k i) =
          (Units.mk0 ζ hζ0) ^ (∑ i, c i) := by
        rw [zpow_eq_zpow_iff_modEq, ← orderOf_units, Units.val_mk0, hζ, hcast]
        exact sum_mul_pow_modEq Finset.univ c k ((p ^ e : ℕ) : ℤ)
      have := congrArg Units.val hu
      simpa only [Units.val_zpow_eq_zpow_val, Units.val_mk0] using this
  · rintro ⟨hn, hnζ⟩
    apply mem_Eset_of_aeval_Pn_eq_zero c p e hq he hr hc hC hζ n
    · intro f hf
      have hle : torusIdeal (F := F) c ≤ RingHom.ker (MvPolynomial.aeval (Pn n) : MvPolynomial F F →ₐ[F] RatFunc F).toRingHom := by
        rw [← hT, Ideal.span_le]
        intro g hg
        exact RingHom.mem_ker.2 (hn g hg)
      exact RingHom.mem_ker.1 (hle hf)
    · rw [sub_eq_zero, ← map_zpow₀, ← map_zpow₀] at hnζ
      exact (algebraMap F (RatFunc F)).injective hnζ

/-- **Proposition 2.6.** -/
theorem prop26 (p : ℕ) [Fact p.Prime] : Prop26 p := by
  intro e he r c hr hc hC
  haveI : Fintype (GaloisField p e) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p e) = p ^ e := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p e (by omega)]
  have := Eset_mem_RClass_ratFunc (F := GaloisField p e) p e hcard he c hr hc hC
  exact RClass.descent_ratFunc (F := ZMod p) (L := GaloisField p e) this

/-- **Proposition 2.7.** -/
theorem prop27 (p : ℕ) [Fact p.Prime] : Prop27 p := prop27_of_prop26 (prop26 p)

/-- **Theorem 2.2** (unconditional): every `p`-normal set is the zero set of a linear recurrence
sequence over `𝔽_p(t)`. -/
theorem theorem22 (p : ℕ) [Fact p.Prime] : Theorem22 p := theorem22_of_prop27 (prop27 p)

end ArithDyn.Derksen
