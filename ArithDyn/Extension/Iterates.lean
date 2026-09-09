import ArithDyn.Extension.Theorem31

/-!
# Iterates: `Ψ^m ∘ j = j ∘ φ^m` (end of the proof of Theorem 3.1)

Polynomial self-maps are composed by substitution; if `Ψ ∘ j ≡ j ∘ φ (mod I)` and `φ` preserves
`I`, then the same holds for all iterates.
-/

set_option autoImplicit false

namespace ArithDyn.Extension

open MvPolynomial

variable {k : Type*} [CommRing k]

/-- The `m`-fold iterate of a polynomial self-map `Ψ : 𝔸^ν → 𝔸^ν` (composition by substitution;
`iterMap Ψ (m+1) = iterMap Ψ m ∘ Ψ`). -/
noncomputable def iterMap {ν : Type*} (Ψ : ν → MvPolynomial ν k) : ℕ → ν → MvPolynomial ν k
  | 0 => X
  | m + 1 => fun a => aeval Ψ (iterMap Ψ m a)

@[simp] lemma iterMap_zero {ν : Type*} (Ψ : ν → MvPolynomial ν k) : iterMap Ψ 0 = X := rfl

lemma iterMap_succ {ν : Type*} (Ψ : ν → MvPolynomial ν k) (m : ℕ) (a : ν) :
    iterMap Ψ (m + 1) a = aeval Ψ (iterMap Ψ m a) := rfl

/-- Compatibility of iterates modulo an ideal preserved by `f`. -/
theorem iterMap_compat {ν σ : Type*} (I : Ideal (MvPolynomial σ k)) (j : ν → MvPolynomial σ k)
    (Ψ : ν → MvPolynomial ν k) (f : σ → MvPolynomial σ k)
    (hpres : ∀ g ∈ I, aeval f g ∈ I)
    (hcomm : ∀ a, aeval j (Ψ a) - aeval f (j a) ∈ I) :
    ∀ (m : ℕ) (a : ν), aeval j (iterMap Ψ m a) - aeval (iterMap f m) (j a) ∈ I := by
  intro m
  induction m with
  | zero =>
    intro a
    simp [iterMap]
  | succ m ih =>
    intro a
    -- work modulo `I`
    rw [← Ideal.Quotient.eq]
    have e1 : ∀ (g : ν → MvPolynomial σ k) (q : MvPolynomial ν k),
        Ideal.Quotient.mk I (aeval g q) = aeval (fun b => Ideal.Quotient.mk I (g b)) q := by
      intro g q
      have := AlgHom.congr_fun (comp_aeval g (Ideal.Quotient.mkₐ k I)) q
      simpa using this
    have key : ∀ p : MvPolynomial ν k,
        Ideal.Quotient.mk I (aeval j (aeval Ψ p)) = Ideal.Quotient.mk I (aeval f (aeval j p)) := by
      intro p
      rw [← AlgHom.comp_apply (aeval j) (aeval Ψ), comp_aeval,
        ← AlgHom.comp_apply (aeval f) (aeval j), comp_aeval, e1, e1]
      congr 2
      funext b
      exact Ideal.Quotient.eq.2 (hcomm b)
    rw [iterMap_succ, key]
    have h3 : (fun b => aeval f (iterMap f m b)) = iterMap f (m + 1) := rfl
    have h2 : aeval (fun b => aeval f (iterMap f m b)) (j a) =
        aeval f (aeval (iterMap f m) (j a)) := by
      rw [← AlgHom.comp_apply (aeval f) (aeval (iterMap f m)), comp_aeval]
    rw [← h3, h2]
    -- `aeval f` respects congruence modulo `I` since `f` preserves `I`
    have h4 := ih a
    rw [Ideal.Quotient.eq]
    have : aeval f (aeval j (iterMap Ψ m a)) - aeval f (aeval (iterMap f m) (j a)) =
        aeval f (aeval j (iterMap Ψ m a) - aeval (iterMap f m) (j a)) := by rw [map_sub]
    rw [this]
    exact hpres _ h4

/-- **Theorem 3.1, last sentence**: the extension commutes with all iterates. -/
theorem theorem_3_1_iterates {K : Type*} [Field K] {r : ℕ}
    (I : Ideal (MvPolynomial (Fin (r + 1)) K)) (f : Fin (r + 1) → MvPolynomial (Fin (r + 1)) K)
    (hpres : ∀ g ∈ I, aeval f g ∈ I) {ν : Type} (j : ν → MvPolynomial (Fin (r + 1)) K)
    (Ψ : ν → MvPolynomial ν K) (hcomm : ∀ m, aeval j (Ψ m) - aeval f (j m) ∈ I) :
    ∀ (m : ℕ) (a : ν), aeval j (iterMap Ψ m a) - aeval (iterMap f m) (j a) ∈ I :=
  iterMap_compat I j Ψ f hpres hcomm

end ArithDyn.Extension
