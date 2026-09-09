import ArithDyn.Nilpotence.Main

/-!
# Irreducibility of the surfaces `Y_q` (paper Lemma 5.6)

`Y_q = {y^q = x z^{q-1}} ⊆ 𝔸³` is the zero set of `f_q = y^q - x z^{q-1}`. Viewed as a polynomial
in `x` over `K[y,z]`, `f_q = -z^{q-1} · x + y^q` is linear with coprime coefficients, hence
irreducible; so `f_q` is prime in the UFD `K[x,y,z]`. Over an algebraically closed field the
Nullstellensatz gives `I(Y_q) = (f_q)`, a prime ideal, and therefore `Y_q` is irreducible: it is
nonempty and is not covered by two closed sets unless it lies in one of them.
-/

set_option autoImplicit false

namespace ArithDyn.Nilpotence

open MvPolynomial

variable {K : Type*} [Field K]

/-- The defining polynomial `y^q - x z^{q-1}` of `Y_q`. -/
noncomputable def fs (q : ℕ) : MvPolynomial (Fin 3) K := X 1 ^ q - X 0 * X 2 ^ (q - 1)

/-- Over a domain, a linear polynomial `a X + b` with `a ≠ 0` and `a, b` coprime is irreducible. -/
lemma irreducible_linear {R : Type*} [CommRing R] [IsDomain R] {a b : R} (ha : a ≠ 0)
    (hab : IsRelPrime b a) : Irreducible (Polynomial.C a * Polynomial.X + Polynomial.C b) := by
  refine Polynomial.irreducible_of_degree_eq_one_of_isRelPrime_coeff
    (Polynomial.degree_linear ha) ?_
  simpa [Polynomial.coeff_C] using hab

/-- The variables `X 0` and `X 1` of `K[y,z]` are coprime. -/
lemma isRelPrime_X_zero_X_one : IsRelPrime (X 0 : MvPolynomial (Fin 2) K) (X 1) :=
  (MvPolynomial.X_prime (i := (0 : Fin 2))).irreducible.isRelPrime_iff_not_dvd.2
    (by rw [MvPolynomial.X_dvd_X]; decide)

/-- Under `finSuccEquiv K 2` (`x ↦ X`, `y ↦ C y`, `z ↦ C z`), `f_{k+1}` becomes the linear
polynomial `-z^k · X + y^{k+1}` over `K[y,z]`. -/
lemma finSuccEquiv_fs (k : ℕ) :
    finSuccEquiv K 2 (fs (K := K) (k + 1)) =
      Polynomial.C (-(X 1 ^ k)) * Polynomial.X + Polynomial.C (X 0 ^ (k + 1)) := by
  have e1 : finSuccEquiv K 2 (X 1 : MvPolynomial (Fin 3) K) = Polynomial.C (X 0) :=
    finSuccEquiv_X_succ (j := (0 : Fin 2))
  have e2 : finSuccEquiv K 2 (X 2 : MvPolynomial (Fin 3) K) = Polynomial.C (X 1) :=
    finSuccEquiv_X_succ (j := (1 : Fin 2))
  simp only [fs, Nat.add_sub_cancel, map_sub, map_pow, map_mul, finSuccEquiv_X_zero, e1, e2,
    map_neg]
  ring

/-- `f_q = y^q - x z^{q-1}` is irreducible in `K[x,y,z]` (any field `K`). -/
theorem irreducible_fs {q : ℕ} (hq : 1 ≤ q) : Irreducible (fs (K := K) q) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have hrel : IsRelPrime ((X 0 : MvPolynomial (Fin 2) K) ^ (k + 1)) (-(X 1 ^ k)) :=
    isRelPrime_X_zero_X_one.pow.neg_right
  have key : Irreducible (finSuccEquiv K 2 (fs (K := K) (k + 1))) := by
    rw [finSuccEquiv_fs]
    exact irreducible_linear (neg_ne_zero.2 (pow_ne_zero _ (MvPolynomial.X_ne_zero 1))) hrel
  exact (MulEquiv.irreducible_iff (finSuccEquiv K 2)).1 key

/-- `f_q` is prime: `K[x,y,z]` is a unique factorisation domain. -/
theorem prime_fs {q : ℕ} (hq : 1 ≤ q) : Prime (fs (K := K) q) :=
  (irreducible_fs hq).prime

/-- `Y_q` is the zero locus of the ideal `(f_q)`. -/
lemma Ysurf_eq_zeroLocus (q : ℕ) :
    Ysurf (K := K) q = zeroLocus K (Ideal.span {fs (K := K) q}) := by
  rw [zeroLocus_span]
  ext a
  simp [Ysurf, fs, sub_eq_zero]

/-- **Nullstellensatz for `Y_q`**: over an algebraically closed field, `I(Y_q) = (f_q)`. -/
theorem vanishingIdeal_Ysurf [IsAlgClosed K] {q : ℕ} (hq : 1 ≤ q) :
    MvPolynomial.vanishingIdeal K (Ysurf (K := K) q) = Ideal.span {fs q} := by
  rw [Ysurf_eq_zeroLocus, vanishingIdeal_zeroLocus_eq_radical]
  exact ((Ideal.span_singleton_prime (irreducible_fs hq).ne_zero).2 (prime_fs hq)).radical

/-- The vanishing ideal of `Y_q` is prime. -/
theorem isPrime_vanishingIdeal_Ysurf [IsAlgClosed K] {q : ℕ} (hq : 1 ≤ q) :
    (MvPolynomial.vanishingIdeal K (Ysurf (K := K) q)).IsPrime := by
  rw [vanishingIdeal_Ysurf hq]
  exact (Ideal.span_singleton_prime (irreducible_fs hq).ne_zero).2 (prime_fs hq)

/-- A set of points with prime vanishing ideal is not covered by two closed sets `V A ∪ V B`
unless it lies in one of them. -/
lemma subset_or_subset_of_isPrime_vanishingIdeal {Y : Set (Fin 3 → K)}
    (hP : (MvPolynomial.vanishingIdeal K Y).IsPrime) {A B : Set (MvPolynomial (Fin 3) K)}
    (h : Y ⊆ V A ∪ V B) : Y ⊆ V A ∨ Y ⊆ V B := by
  -- a point outside `V C` witnesses a polynomial of `C` not vanishing there
  have hex : ∀ {C : Set (MvPolynomial (Fin 3) K)} {y : Fin 3 → K}, y ∉ V C →
      ∃ c ∈ C, eval y c ≠ 0 := by
    intro C y hy
    by_contra hne
    simp only [not_exists, not_and, ne_eq, not_not] at hne
    exact hy (fun c hc => hne c hc)
  by_contra hcon
  rw [not_or, Set.not_subset, Set.not_subset] at hcon
  obtain ⟨⟨y₁, hy₁, hy₁A⟩, ⟨y₂, hy₂, hy₂B⟩⟩ := hcon
  obtain ⟨a, ha, hay₁⟩ := hex hy₁A
  obtain ⟨b, hb, hby₂⟩ := hex hy₂B
  -- `a * b` vanishes on all of `Y`
  have hab : a * b ∈ MvPolynomial.vanishingIdeal K Y := by
    rw [mem_vanishingIdeal_iff]
    intro y hy
    rw [aeval_eq_eval, map_mul]
    rcases h hy with hyA | hyB
    · rw [hyA a ha, zero_mul]
    · rw [hyB b hb, mul_zero]
  rcases hP.mem_or_mem hab with h1 | h1
  · rw [mem_vanishingIdeal_iff] at h1
    have := h1 y₁ hy₁
    rw [aeval_eq_eval] at this
    exact hay₁ this
  · rw [mem_vanishingIdeal_iff] at h1
    have := h1 y₂ hy₂
    rw [aeval_eq_eval] at this
    exact hby₂ this

/-- Zariski irreducibility of `Y_q` (Lemma 5.6). -/
theorem Ysurf_irreducible [IsAlgClosed K] {q : ℕ} (hq : 1 ≤ q) :
    (Ysurf (K := K) q).Nonempty ∧
    ∀ A B : Set (MvPolynomial (Fin 3) K), Ysurf q ⊆ V A ∪ V B → Ysurf q ⊆ V A ∨ Ysurf q ⊆ V B :=
  ⟨⟨_, param_mem_Ysurf hq 1 1⟩, fun _ _ h =>
    subset_or_subset_of_isPrime_vanishingIdeal (isPrime_vanishingIdeal_Ysurf hq) h⟩

/-- `f_q` is defined over the prime field: it is the image of the same polynomial over `ZMod p`. -/
lemma fs_eq_map (p : ℕ) [Fact p.Prime] (q : ℕ) :
    fs (K := AlgebraicClosure (ZMod p)) q =
      MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) (fs q) := by
  simp [fs]

/-- **Theorem 5.2 over `\bar 𝔽_p`, all clauses**: `O` is the unique fixed point; each `Y_s`
(`s ≥ 1`) is defined over `𝔽_p`, Zariski-irreducible, geometrically nilpotent but not nilpotent;
and (5.4) holds for every closed geometrically nilpotent `Y = V F`. -/
theorem theorem_5_2' (p : ℕ) [Fact p.Prime]
    (F : Set (MvPolynomial (Fin 3) (AlgebraicClosure (ZMod p))))
    (hnil : GeomNilpotent (V F)) :
    (∀ a : Fin 3 → AlgebraicClosure (ZMod p), T a = a ↔ a = 0) ∧
    (∀ s, 1 ≤ s → Ysurf (K := AlgebraicClosure (ZMod p)) (p ^ s) =
      V {MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) (fs (p ^ s))}) ∧
    (∀ s, 1 ≤ s → (Ysurf (K := AlgebraicClosure (ZMod p)) (p ^ s)).Nonempty ∧
      ∀ A B : Set (MvPolynomial (Fin 3) (AlgebraicClosure (ZMod p))),
        Ysurf (p ^ s) ⊆ V A ∪ V B → Ysurf (p ^ s) ⊆ V A ∨ Ysurf (p ^ s) ⊆ V B) ∧
    (∀ s, 1 ≤ s → GeomNilpotent (Ysurf (K := AlgebraicClosure (ZMod p)) (p ^ s))) ∧
    (∀ s, 1 ≤ s → ∀ N, ∃ a ∈ Ysurf (K := AlgebraicClosure (ZMod p)) (p ^ s), T^[N] a ≠ 0) ∧
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ k m : ℕ,
      ¬ (T^[k] '' Ysurf (p ^ s) ⊆ zariskiClosure (T^[m] '' V F)) := by
  obtain ⟨h1, h3, h4, h5⟩ := theorem_5_2 p F hnil
  have hq : ∀ s : ℕ, 1 ≤ p ^ s := fun s => Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  refine ⟨h1, fun s _ => ?_, fun s _ => Ysurf_irreducible (hq s), h3, h4, h5⟩
  rw [← fs_eq_map, Ysurf_eq_V]
  rfl

end ArithDyn.Nilpotence
