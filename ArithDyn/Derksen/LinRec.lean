import Mathlib

/-!
# Linear recurrence sequences via finite-dimensional linear representations (paper §2.2)

A one-sided sequence `u : ℕ → K` is a *linear recurrence sequence* iff it has a representation
`u n = ℓ Aⁿ v` with a square matrix `A` (Cayley–Hamilton in one direction, the companion matrix
in the other). We set up this representation, prove closure under sums, Hadamard products,
shifts, dilations and finite modifications, and prove the equivalence with Mathlib's
`LinearRecurrence.IsSolution` (a monic constant-coefficient recurrence valid from `n = 0`).
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

open Matrix Finset
open scoped Kronecker

universe u

variable {K : Type u} [Field K]

/-- A finite-dimensional linear representation `n ↦ ℓ Aⁿ v` of a one-sided sequence, with state
space indexed by `ι`. -/
structure LinRep (K : Type u) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] where
  A : Matrix ι ι K
  ℓ : ι → K
  v : ι → K

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

namespace LinRep

/-- The represented sequence `n ↦ ℓ Aⁿ v`. -/
def seq (r : LinRep K ι) (n : ℕ) : K := r.ℓ ⬝ᵥ ((r.A ^ n) *ᵥ r.v)

/-- The constant sequence. -/
def const (c : K) : LinRep K Unit := ⟨1, fun _ => c, fun _ => 1⟩

@[simp] lemma const_seq (c : K) (n : ℕ) : (const c).seq n = c := by
  simp [seq, const, dotProduct, one_pow, Matrix.one_mulVec]

/-- Sum of two represented sequences (block-diagonal state matrix). -/
def add (r : LinRep K ι) (s : LinRep K κ) : LinRep K (ι ⊕ κ) :=
  ⟨Matrix.fromBlocks r.A 0 0 s.A, Sum.elim r.ℓ s.ℓ, Sum.elim r.v s.v⟩

@[simp] lemma add_seq (r : LinRep K ι) (s : LinRep K κ) (n : ℕ) :
    (r.add s).seq n = r.seq n + s.seq n := by
  simp only [seq, add]
  rw [Matrix.fromBlocks_diagonal_pow, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, add_zero, zero_add,
    sumElim_dotProduct_sumElim]

lemma kronecker_pow (A : Matrix ι ι K) (B : Matrix κ κ K) (n : ℕ) :
    (A ⊗ₖ B) ^ n = (A ^ n) ⊗ₖ (B ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, Matrix.one_kronecker_one]
  | succ n ih => rw [pow_succ, pow_succ, pow_succ, ih, Matrix.mul_kronecker_mul]

lemma kronecker_mulVec (A : Matrix ι ι K) (B : Matrix κ κ K) (x : ι → K) (y : κ → K) :
    (A ⊗ₖ B) *ᵥ (fun p => x p.1 * y p.2) = fun p => (A *ᵥ x) p.1 * (B *ᵥ y) p.2 := by
  funext ⟨i, j⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

lemma dotProduct_prod (ℓ : ι → K) (ℓ' : κ → K) (x : ι → K) (y : κ → K) :
    (fun p : ι × κ => ℓ p.1 * ℓ' p.2) ⬝ᵥ (fun p => x p.1 * y p.2) = (ℓ ⬝ᵥ x) * (ℓ' ⬝ᵥ y) := by
  simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

/-- Hadamard product of two represented sequences (Kronecker product of state matrices). -/
def mul (r : LinRep K ι) (s : LinRep K κ) : LinRep K (ι × κ) :=
  ⟨r.A ⊗ₖ s.A, fun p => r.ℓ p.1 * s.ℓ p.2, fun p => r.v p.1 * s.v p.2⟩

@[simp] lemma mul_seq (r : LinRep K ι) (s : LinRep K κ) (n : ℕ) :
    (r.mul s).seq n = r.seq n * s.seq n := by
  simp only [seq, mul]
  rw [kronecker_pow, kronecker_mulVec, dotProduct_prod]

lemma pow_mulVec_pow (A : Matrix ι ι K) (m n : ℕ) (v : ι → K) :
    A ^ m *ᵥ (A ^ n *ᵥ v) = A ^ (m + n) *ᵥ v := by
  rw [pow_add]
  exact Matrix.mulVec_mulVec _ _ _

/-- Shift `n ↦ n + b`. -/
def shift (r : LinRep K ι) (b : ℕ) : LinRep K ι := ⟨r.A, r.ℓ, r.A ^ b *ᵥ r.v⟩

@[simp] lemma shift_seq (r : LinRep K ι) (b n : ℕ) : (r.shift b).seq n = r.seq (n + b) := by
  simp only [seq, shift]
  rw [pow_mulVec_pow]

/-- Dilation `n ↦ a n`. -/
def dilate (r : LinRep K ι) (a : ℕ) : LinRep K ι := ⟨r.A ^ a, r.ℓ, r.v⟩

@[simp] lemma dilate_seq (r : LinRep K ι) (a n : ℕ) : (r.dilate a).seq n = r.seq (a * n) := by
  simp only [seq, dilate]
  rw [pow_mul]

/-- Scalar multiple. -/
def smul (c : K) (r : LinRep K ι) : LinRep K ι := ⟨r.A, c • r.ℓ, r.v⟩

@[simp] lemma smul_seq (c : K) (r : LinRep K ι) (n : ℕ) : (smul c r).seq n = c * r.seq n := by
  simp only [seq, smul, smul_dotProduct, smul_eq_mul]

end LinRep

/-- `u` is a linear recurrence sequence: it has a finite-dimensional linear representation. -/
def IsLinRecSeq (u : ℕ → K) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (r : LinRep K ι), r.seq = u

namespace IsLinRecSeq

lemma of_rep (r : LinRep K ι) : IsLinRecSeq r.seq := ⟨ι, inferInstance, inferInstance, r, rfl⟩

lemma const (c : K) : IsLinRecSeq (fun _ : ℕ => c) :=
  ⟨Unit, inferInstance, inferInstance, LinRep.const c, funext (LinRep.const_seq c)⟩

lemma add {u v : ℕ → K} (hu : IsLinRecSeq u) (hv : IsLinRecSeq v) : IsLinRecSeq (u + v) := by
  obtain ⟨ι, _, _, r, rfl⟩ := hu
  obtain ⟨κ, _, _, s, rfl⟩ := hv
  exact ⟨ι ⊕ κ, inferInstance, inferInstance, r.add s, funext (fun n => by simp)⟩

lemma mul {u v : ℕ → K} (hu : IsLinRecSeq u) (hv : IsLinRecSeq v) : IsLinRecSeq (u * v) := by
  obtain ⟨ι, _, _, r, rfl⟩ := hu
  obtain ⟨κ, _, _, s, rfl⟩ := hv
  exact ⟨ι × κ, inferInstance, inferInstance, r.mul s, funext (fun n => by simp)⟩

lemma smul (c : K) {u : ℕ → K} (hu : IsLinRecSeq u) : IsLinRecSeq (fun n => c * u n) := by
  obtain ⟨ι, _, _, r, rfl⟩ := hu
  exact ⟨ι, inferInstance, inferInstance, LinRep.smul c r, funext (fun n => by simp)⟩

lemma shift {u : ℕ → K} (hu : IsLinRecSeq u) (b : ℕ) : IsLinRecSeq (fun n => u (n + b)) := by
  obtain ⟨ι, _, _, r, rfl⟩ := hu
  exact ⟨ι, inferInstance, inferInstance, r.shift b, funext (fun n => by simp)⟩

lemma dilate {u : ℕ → K} (hu : IsLinRecSeq u) (a : ℕ) : IsLinRecSeq (fun n => u (a * n)) := by
  obtain ⟨ι, _, _, r, rfl⟩ := hu
  exact ⟨ι, inferInstance, inferInstance, r.dilate a, funext (fun n => by simp)⟩

lemma congr {u v : ℕ → K} (hu : IsLinRecSeq u) (h : ∀ n, u n = v n) : IsLinRecSeq v := by
  obtain ⟨ι, _, _, r, rfl⟩ := hu
  exact ⟨ι, inferInstance, inferInstance, r, funext h⟩

lemma sum {α : Type*} (s : Finset α) (f : α → ℕ → K) (h : ∀ i ∈ s, IsLinRecSeq (f i)) :
    IsLinRecSeq (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (const (0 : K)).congr (fun n => by simp)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end IsLinRecSeq

/-! ### Equivalence with Mathlib's `LinearRecurrence.IsSolution` -/

/-- Companion-matrix direction: a solution of a monic constant-coefficient recurrence has a
linear representation. -/
theorem isLinRecSeq_of_isSolution (E : LinearRecurrence K) {u : ℕ → K} (hu : E.IsSolution u) :
    IsLinRecSeq u := by
  classical
  rcases Nat.eq_zero_or_pos E.order with h0 | hpos
  · -- order `0`: `u = 0`
    refine (IsLinRecSeq.const (0 : K)).congr (fun n => ?_)
    have h := hu n
    haveI : IsEmpty (Fin E.order) := by rw [h0]; infer_instance
    rw [Finset.univ_eq_empty, Finset.sum_empty, h0, add_zero] at h
    exact h.symm
  · let A : Matrix (Fin E.order) (Fin E.order) K := LinearMap.toMatrix' E.tupleSucc
    have hA : ∀ x : Fin E.order → K, A *ᵥ x = E.tupleSucc x := fun x =>
      LinearMap.toMatrix'_mulVec _ _
    -- `Aⁿ (u₀, …, u_{d-1}) = (u_n, …, u_{n+d-1})`
    have key : ∀ n : ℕ, (A ^ n) *ᵥ (fun i : Fin E.order => u i) =
        fun i : Fin E.order => u (n + i) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h1 : (A ^ (n + 1)) *ᵥ (fun i : Fin E.order => u i) =
            A *ᵥ (A ^ n *ᵥ (fun i : Fin E.order => u i)) := by
          rw [pow_succ']
          exact (Matrix.mulVec_mulVec _ _ _).symm
        rw [h1, ih, hA]
        funext i
        simp only [LinearRecurrence.tupleSucc, LinearMap.coe_mk, AddHom.coe_mk]
        split_ifs with h
        · show u (n + ((i : ℕ) + 1)) = u (n + 1 + (i : ℕ))
          congr 1; omega
        · have hi : (i : ℕ) + 1 = E.order := by have := i.isLt; omega
          rw [show n + 1 + (i : ℕ) = n + E.order by omega, hu n]
    refine ⟨Fin E.order, inferInstance, inferInstance, ⟨A, Pi.single ⟨0, hpos⟩ 1, fun i => u i⟩,
      funext (fun n => ?_)⟩
    simp only [LinRep.seq]
    rw [key n, single_dotProduct, one_mul]
    simp

/-- Cayley–Hamilton direction: a represented sequence satisfies a monic recurrence of order
`dim`, with coefficients read off the characteristic polynomial of the state matrix. -/
theorem exists_isSolution_of_isLinRecSeq {u : ℕ → K} (hu : IsLinRecSeq u) :
    ∃ E : LinearRecurrence K, E.IsSolution u := by
  classical
  obtain ⟨ι, _, _, r, rfl⟩ := hu
  set p := r.A.charpoly with hp
  have hmonic : p.Monic := Matrix.charpoly_monic r.A
  have hdeg : p.natDegree = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim r.A
  set d := Fintype.card ι with hd
  -- Cayley–Hamilton: `A^d = - ∑_{i<d} p.coeff i • A^i`
  have hCH : r.A ^ d = -∑ i ∈ range d, p.coeff i • r.A ^ i := by
    have h0 := Matrix.aeval_self_charpoly r.A
    rw [← hp, hmonic.as_sum, hdeg] at h0
    simp only [map_add, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h0
    exact eq_neg_of_add_eq_zero_left h0
  -- as an identity of vectors
  have hCH' : ∀ w : ι → K, r.A ^ d *ᵥ w = -∑ i ∈ range d, p.coeff i • (r.A ^ i *ᵥ w) := by
    intro w
    rw [hCH, Matrix.neg_mulVec, Matrix.sum_mulVec]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.smul_mulVec]
  refine ⟨⟨d, fun i => -p.coeff i⟩, fun n => ?_⟩
  show r.ℓ ⬝ᵥ (r.A ^ (n + d) *ᵥ r.v) = ∑ i : Fin d, -p.coeff i * (r.ℓ ⬝ᵥ (r.A ^ (n + i) *ᵥ r.v))
  have h1 : r.A ^ (n + d) *ᵥ r.v = r.A ^ n *ᵥ (r.A ^ d *ᵥ r.v) :=
    (LinRep.pow_mulVec_pow _ _ _ _).symm
  rw [h1, hCH', Matrix.mulVec_neg, Matrix.mulVec_sum, dotProduct_neg, dotProduct_sum,
    ← Fin.sum_univ_eq_sum_range, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mulVec_smul, LinRep.pow_mulVec_pow, dotProduct_smul, smul_eq_mul, neg_mul]

/-- The two notions agree. -/
theorem isLinRecSeq_iff (u : ℕ → K) :
    IsLinRecSeq u ↔ ∃ E : LinearRecurrence K, E.IsSolution u :=
  ⟨exists_isSolution_of_isLinRecSeq, fun ⟨E, hE⟩ => isLinRecSeq_of_isSolution E hE⟩

/-! ### Basic building blocks: finite support and periodic sequences -/

/-- A sequence with finite support is a linear recurrence sequence (recurrence `u (n + N) = 0`). -/
theorem isLinRecSeq_of_eventually_zero {u : ℕ → K} {N : ℕ} (h : ∀ n, N ≤ n → u n = 0) :
    IsLinRecSeq u :=
  isLinRecSeq_of_isSolution ⟨N, fun _ => 0⟩ (fun n => by
    show u (n + N) = ∑ i : Fin N, (0 : K) * u (n + i)
    simp only [zero_mul, Finset.sum_const_zero]
    exact h _ (by omega))

/-- A periodic sequence is a linear recurrence sequence (recurrence `u (n + a) = u n`). -/
theorem isLinRecSeq_of_periodic {u : ℕ → K} {a : ℕ} (ha : 0 < a) (h : ∀ n, u (n + a) = u n) :
    IsLinRecSeq u :=
  isLinRecSeq_of_isSolution ⟨a, Pi.single ⟨0, ha⟩ 1⟩ (fun n => by
    show u (n + a) = ∑ i : Fin a, (Pi.single (⟨0, ha⟩ : Fin a) (1 : K) : Fin a → K) i * u (n + i)
    rw [h n, Finset.sum_eq_single ⟨0, ha⟩]
    · simp
    · intro i _ hi
      simp [Pi.single_apply, hi]
    · intro h'; exact absurd (Finset.mem_univ _) h')

/-- Changing finitely many values preserves the property. -/
theorem IsLinRecSeq.modify {u : ℕ → K} (hu : IsLinRecSeq u) (S : Finset ℕ) (w : ℕ → K) :
    IsLinRecSeq (fun n => if n ∈ S then w n else u n) := by
  have hdiff : IsLinRecSeq (fun n => (if n ∈ S then w n else u n) - u n) := by
    apply isLinRecSeq_of_eventually_zero (N := (S.sup id) + 1)
    intro n hn
    have : n ∉ S := fun hnS => by
      have := Finset.le_sup (f := id) hnS
      simp only [id] at this
      omega
    simp [this]
  have := hdiff.add hu
  exact this.congr (fun n => by simp)

end ArithDyn.Derksen
