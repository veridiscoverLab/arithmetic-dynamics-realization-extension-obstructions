import ArithDyn.Density.Map
import ArithDyn.Nilpotence.Dense
import ArithDyn.Nilpotence.FiniteOrder

/-!
# Zariski density of the totally defined locus (paper §4.4, Proposition 4.10)

Over an infinite field `K` in which every nonzero element is a root of unity (e.g. `\bar 𝔽_Q`),
every polynomial `H ∈ K[A,B,Z]` vanishing on the affine cone over `ℙ²(K)_f` is zero; i.e.
`ℙ²(K)_f` is Zariski dense in `ℙ²`.
-/

set_option autoImplicit false

namespace ArithDyn.Density

open MvPolynomial Projectivization ArithDyn.Nilpotence

variable {K : Type*} [Field K]

lemma eval_aeval_fin (g : Fin 3 → MvPolynomial (Fin 3) K) (x : Fin 3 → K)
    (p : MvPolynomial (Fin 3) K) : eval x (aeval g p) = eval (fun i => eval x (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, eval_X, hp]

/-- Proposition 4.10. -/
theorem eq_zero_of_vanish_on_totallyDefined [Infinite K]
    (hfin : ∀ u : K, u ≠ 0 → ∃ M : ℕ, 0 < M ∧ u ^ M = 1)
    (H : MvPolynomial (Fin 3) K)
    (hH : ∀ (v : Fin 3 → K) (hv : v ≠ 0), TotallyDefined (mk K v hv) → eval v H = 0) :
    H = 0 := by
  -- Step 1: `H` vanishes at `c • (v-1, u(v-1), 1)` for `c ≠ 0`, `(u,v) ∈ E` (Lemma 4.4)
  have h1 : ∀ c u v : K, c ≠ 0 → (u, v) ∈ Eset K →
      eval ![c * (v - 1), c * u * (v - 1), c] H = 0 := by
    intro c u v hc hE
    obtain ⟨hu, hv, hu1, hesc⟩ := hE
    have hv1 : v ≠ 1 := by intro h; apply hesc 0; simp [h]
    have hne : (![c * (v - 1), c * u * (v - 1), c] : Fin 3 → K) ≠ 0 := by
      intro h; have := congrFun h 2; simp at this; exact hc this
    have hmk : mk K ![c * (v - 1), c * u * (v - 1), c] hne = Phi u v := by
      rw [Phi, mk_eq_mk_iff']
      exact ⟨c, by ext i; fin_cases i <;> simp <;> ring⟩
    apply hH _ hne
    rw [hmk]
    exact (totallyDefined_Phi_iff hv1).2 hesc
  -- Step 2: substitute `x = c(v-1), y = cu(v-1), z = c` (new variables `X 0 = c, X 1 = v, X 2 = u`)
  set H' : MvPolynomial (Fin 3) K :=
    aeval ![X 0 * (X 1 - 1), X 0 * X 2 * (X 1 - 1), X 0] H with hH'
  have h2 : ∀ c u v : K, c ≠ 0 → (u, v) ∈ Eset K → eval ![c, v, u] H' = 0 := by
    intro c u v hc hE
    rw [hH', eval_aeval_fin]
    have hvec : (fun i => eval ![c, v, u]
        ((![X 0 * (X 1 - 1), X 0 * X 2 * (X 1 - 1), X 0] : Fin 3 → MvPolynomial (Fin 3) K) i)) =
        ![c * (v - 1), c * u * (v - 1), c] := by
      funext i; fin_cases i <;> simp <;> ring
    rw [hvec]
    exact h1 c u v hc hE
  -- Step 3: `H' = 0`, by density of `E` in the `(v,u)`-plane and of `K \ {0}` in the `c`-line
  have h3 : H' = 0 := by
    have hQ : ∀ i, (finSuccEquiv K 2 H').coeff i = 0 := by
      intro i
      apply eq_zero_of_vanish_on_Eset hfin
      rintro ⟨u, v⟩ hE
      have hpoly : Polynomial.map (eval ![v, u]) (finSuccEquiv K 2 H') = 0 := by
        apply Polynomial.eq_zero_of_infinite_isRoot
        apply ((Set.finite_singleton (0 : K)).infinite_compl).mono
        intro c hc
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
        show Polynomial.IsRoot _ c
        rw [Polynomial.IsRoot, ← eval_eq_eval_mv_eval']
        exact h2 c u v hc hE
      have := congrArg (fun q => Polynomial.coeff q i) hpoly
      simpa [Polynomial.coeff_map] using this
    have h0 : finSuccEquiv K 2 H' = 0 :=
      Polynomial.ext (fun i => by rw [hQ i, Polynomial.coeff_zero])
    have := congrArg (finSuccEquiv K 2).symm h0
    simpa using this
  -- Step 4: `H` vanishes where `x z ≠ 0`, hence `H * X 0 * X 2 = 0`, hence `H = 0`
  have h4 : H * (X 0 * X 2) = 0 := by
    apply MvPolynomial.funext
    intro a
    simp only [map_mul, eval_X, map_zero]
    by_cases hx : a 0 = 0
    · simp [hx]
    by_cases hz : a 2 = 0
    · simp [hz]
    have hvec : (fun i => eval ![a 2, a 0 / a 2 + 1, a 1 / a 0]
        ((![X 0 * (X 1 - 1), X 0 * X 2 * (X 1 - 1), X 0] : Fin 3 → MvPolynomial (Fin 3) K) i)) =
        a := by
      funext i; fin_cases i <;> simp <;> field_simp
    have key : eval a H = eval ![a 2, a 0 / a 2 + 1, a 1 / a 0] H' := by
      rw [hH', eval_aeval_fin, hvec]
    rw [key, h3, map_zero, zero_mul]
  have hX : (X 0 * X 2 : MvPolynomial (Fin 3) K) ≠ 0 := mul_ne_zero (X_ne_zero 0) (X_ne_zero 2)
  exact (mul_eq_zero.1 h4).resolve_right hX

/-- Proposition 4.10 over `\bar 𝔽_p`: `ℙ²(\bar 𝔽_p)_f` is Zariski dense. -/
theorem prop_4_10 (p : ℕ) [Fact p.Prime]
    (H : MvPolynomial (Fin 3) (AlgebraicClosure (ZMod p)))
    (hH : ∀ (v : Fin 3 → AlgebraicClosure (ZMod p)) (hv : v ≠ 0),
      TotallyDefined (mk _ v hv) → eval v H = 0) : H = 0 :=
  eq_zero_of_vanish_on_totallyDefined (forall_exists_pow_eq_one p) H hH

end ArithDyn.Density
