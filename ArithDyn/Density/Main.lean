import ArithDyn.Density.Density
import ArithDyn.Density.Basepoints

/-!
# Theorem 4.2 and Corollary 4.9 for the concrete fields `𝔽_{p^n} = GaloisField p n`
-/

set_option autoImplicit false

namespace ArithDyn.Density

open Filter Topology

noncomputable instance instFintypeGaloisField (p n : ℕ) [Fact p.Prime] :
    Fintype (GaloisField p n) := Fintype.ofFinite _

lemma card_galoisField (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    Fintype.card (GaloisField p n) = p ^ n := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]

/-- (4.6) for `𝔽_{p^n}`: `#ℙ²(𝔽_{p^n})_f + 𝓐(p^n - 1) + 3 = p^{2n} + p^n + 1`. -/
theorem exact_count_galoisField (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    Nat.card {P : P2 (GaloisField p n) // TotallyDefined P} + (A (p ^ n - 1) + 3) =
      (p ^ n) ^ 2 + p ^ n + 1 := by
  classical
  have := card_totallyDefined (K := GaloisField p n)
  rwa [card_galoisField p hn] at this

lemma card_galoisField_family (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) :
    ∀ k, 1 ≤ k → Fintype.card (GaloisField p (m * k)) = (p ^ m) ^ k := by
  intro k hk
  rw [card_galoisField p (Nat.pos_iff_ne_zero.1 (Nat.mul_pos hm hk)), ← pow_mul]

lemma two_le_pow (p m : ℕ) [hp : Fact p.Prime] (hm : 1 ≤ m) : 2 ≤ p ^ m :=
  le_trans hp.out.two_le (Nat.le_self_pow (by omega) p)

/-- Theorem 4.2 (4.8), liminf, over `𝔽_Q` with `Q = p^m`: the fields `𝔽_{Q^k} = GaloisField p (m k)`. -/
theorem liminf_density_galoisField (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) :
    liminf (densityFamily (fun k => GaloisField p (m * k)) (p ^ m)) atTop = 1 - M (p ^ m - 1) :=
  liminf_density _ (two_le_pow p m hm) (card_galoisField_family p m hm)

/-- Theorem 4.2 (4.8), limsup. -/
theorem limsup_density_galoisField (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) :
    limsup (densityFamily (fun k => GaloisField p (m * k)) (p ^ m)) atTop = 1 :=
  limsup_density _ (two_le_pow p m hm) (card_galoisField_family p m hm)

/-- Theorem 4.2: the density never converges. -/
theorem density_not_convergent_galoisField (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) :
    ¬ ∃ c : ℝ, Tendsto (densityFamily (fun k => GaloisField p (m * k)) (p ^ m)) atTop (𝓝 c) :=
  density_not_convergent _ (two_le_pow p m hm) (card_galoisField_family p m hm)

/-- Corollary 4.9 over `𝔽₂`: `liminf_k #ℙ²(𝔽_{2^k})_f / #ℙ²(𝔽_{2^k}) = 0`. -/
theorem liminf_density_two_galoisField :
    liminf (densityFamily (fun k => GaloisField 2 k) 2) atTop = 0 :=
  liminf_density_two _ (fun k hk => card_galoisField 2 (by omega))

/-- Corollary 4.9: Conjecture 18.10(b) fails for `f` over `𝔽₂`. -/
theorem not_tendsto_one_galoisField :
    ¬ Tendsto (densityFamily (fun k => GaloisField 2 k) 2) atTop (𝓝 1) :=
  not_tendsto_one _ (fun k hk => card_galoisField 2 (by omega))

end ArithDyn.Density
