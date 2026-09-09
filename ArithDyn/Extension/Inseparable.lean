import Mathlib

/-!
# Example 3.5: separability is needed in Lemma 3.4 (paper §3.2)

In characteristic `2`, with `a ∈ k` and `K = k(α)`, `α² = a`, the pair `F(u,v) = (u², v²)`
has only the trivial common zero, but the restriction-of-scalars system
`G(x₁,y₁,x₂,y₂) = (x₁² + a y₁², 0, x₂² + a y₂², 0)` vanishes at the nonzero geometric vector
`(α, 1, 0, 0)`. We record both computations.
-/

set_option autoImplicit false

namespace ArithDyn.Extension

variable {L : Type*} [Field L]

/-- `F(u,v) = (u², v²)` has only the trivial common zero (over any field). -/
theorem F_trivial_zero (u v : L) (h1 : u ^ 2 = 0) (h2 : v ^ 2 = 0) : u = 0 ∧ v = 0 :=
  ⟨pow_eq_zero_iff (two_ne_zero) |>.1 h1, pow_eq_zero_iff (two_ne_zero) |>.1 h2⟩

/-- In characteristic `2`, if `α² = a` then `(α, 1, 0, 0)` is a nonzero common zero of the
restricted system `G`. -/
theorem G_nontrivial_zero [CharP L 2] (a α : L) (hα : α ^ 2 = a) :
    α ^ 2 + a * 1 ^ 2 = 0 ∧ (0 : L) ^ 2 + a * 0 ^ 2 = 0 ∧
      ((α, (1 : L), (0 : L), (0 : L)) ≠ (0, 0, 0, 0)) := by
  refine ⟨?_, by simp, ?_⟩
  · rw [hα, one_pow, mul_one]
    have : (2 : L) = 0 := CharP.cast_eq_zero L 2
    linear_combination this * a
  · intro h
    have := congrArg (fun p => p.2.1) h
    simp at this

end ArithDyn.Extension
