import ArithDyn.Derksen.LinRec

/-!
# Fundamental bi-infinite recurrences and the class `𝓡` (paper §2.2, (2.1), Lemma 2.3)

A fundamental bi-infinite recurrence is `n ↦ ℓ Aⁿ v` (`n ∈ ℤ`) with `A` invertible ((2.1)).
`RClass K` is the class of integer zero sets of such sequences; the paper's `𝓡_p` is
`RClass (RatFunc (ZMod p))`.

Lemma 2.3 (the parts formalised here): `∅`, `ℤ`, singletons (over `F(t)`), finite unions,
integer translations, and preimages under `n ↦ a n + b` are in `RClass`; restriction to `ℕ` gives
a one-sided linear recurrence sequence.
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

open Matrix Finset
open scoped Kronecker

universe u

variable {K : Type u} [Field K]

/-- A fundamental bi-infinite recurrence in state form (2.1): `n ↦ ℓ Aⁿ v`, `A ∈ GL`. -/
structure LinRepZ (K : Type u) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] where
  A : Matrix ι ι K
  hA : IsUnit A.det
  ℓ : ι → K
  v : ι → K

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

namespace LinRepZ

/-- The represented bi-infinite sequence (matrix `zpow`). -/
noncomputable def seq (r : LinRepZ K ι) (n : ℤ) : K := r.ℓ ⬝ᵥ ((r.A ^ n) *ᵥ r.v)

/-- Its integer zero set. -/
def zeroSet (r : LinRepZ K ι) : Set ℤ := {n | r.seq n = 0}

/-- Constant sequence. -/
def const (c : K) : LinRepZ K Unit := ⟨1, by simp, fun _ => c, fun _ => 1⟩

@[simp] lemma const_seq (c : K) (n : ℤ) : (const c).seq n = c := by
  simp [seq, const, dotProduct, Matrix.one_zpow, Matrix.one_mulVec]

/-- Restriction to `ℕ`. -/
def toLinRep (r : LinRepZ K ι) : LinRep K ι := ⟨r.A, r.ℓ, r.v⟩

@[simp] lemma toLinRep_seq (r : LinRepZ K ι) (n : ℕ) : r.toLinRep.seq n = r.seq n := by
  simp only [LinRep.seq, toLinRep, seq, _root_.zpow_natCast]

/-- Translation `n ↦ n + b`. -/
noncomputable def shift (r : LinRepZ K ι) (b : ℤ) : LinRepZ K ι := ⟨r.A, r.hA, r.ℓ, r.A ^ b *ᵥ r.v⟩

@[simp] lemma shift_seq (r : LinRepZ K ι) (b n : ℤ) : (r.shift b).seq n = r.seq (n + b) := by
  simp only [seq, shift]
  rw [Matrix.zpow_add r.hA]
  exact congrArg _ (Matrix.mulVec_mulVec _ _ _)

/-- Preimage under the affine map `n ↦ a n + b`. -/
noncomputable def affine (r : LinRepZ K ι) (a b : ℤ) : LinRepZ K ι :=
  ⟨r.A ^ a, r.hA.det_zpow a, r.ℓ, r.A ^ b *ᵥ r.v⟩

@[simp] lemma affine_seq (r : LinRepZ K ι) (a b n : ℤ) :
    (r.affine a b).seq n = r.seq (a * n + b) := by
  simp only [seq, affine]
  rw [Matrix.zpow_add r.hA, Matrix.zpow_mul r.A r.hA]
  exact congrArg _ (Matrix.mulVec_mulVec _ _ _)

lemma kronecker_inv (A : Matrix ι ι K) (B : Matrix κ κ K) (hA : IsUnit A.det) (hB : IsUnit B.det) :
    (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.mul_kronecker_mul, Matrix.nonsing_inv_mul _ hA, Matrix.nonsing_inv_mul _ hB,
    Matrix.one_kronecker_one]

lemma isUnit_det_kronecker (A : Matrix ι ι K) (B : Matrix κ κ K) (hA : IsUnit A.det)
    (hB : IsUnit B.det) : IsUnit (A ⊗ₖ B).det := by
  rw [Matrix.det_kronecker]
  exact (hA.pow _).mul (hB.pow _)

lemma isUnit_det_pow (A : Matrix ι ι K) (hA : IsUnit A.det) (m : ℕ) : IsUnit (A ^ m).det := by
  rw [Matrix.det_pow]; exact hA.pow m

lemma kronecker_zpow (A : Matrix ι ι K) (B : Matrix κ κ K) (hA : IsUnit A.det) (hB : IsUnit B.det)
    (n : ℤ) : (A ⊗ₖ B) ^ n = (A ^ n) ⊗ₖ (B ^ n) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [_root_.zpow_natCast, _root_.zpow_natCast, _root_.zpow_natCast]
    exact LinRep.kronecker_pow A B m
  · rw [Matrix.zpow_neg_natCast, Matrix.zpow_neg_natCast, Matrix.zpow_neg_natCast,
      LinRep.kronecker_pow]
    exact kronecker_inv _ _ (isUnit_det_pow A hA m) (isUnit_det_pow B hB m)

/-- Hadamard product (zero sets: union). -/
def mul (r : LinRepZ K ι) (s : LinRepZ K κ) : LinRepZ K (ι × κ) :=
  ⟨r.A ⊗ₖ s.A, isUnit_det_kronecker _ _ r.hA s.hA,
    fun p => r.ℓ p.1 * s.ℓ p.2, fun p => r.v p.1 * s.v p.2⟩

@[simp] lemma mul_seq (r : LinRepZ K ι) (s : LinRepZ K κ) (n : ℤ) :
    (r.mul s).seq n = r.seq n * s.seq n := by
  simp only [seq, mul]
  rw [kronecker_zpow _ _ r.hA s.hA, LinRep.kronecker_mulVec, LinRep.dotProduct_prod]

lemma zeroSet_mul (r : LinRepZ K ι) (s : LinRepZ K κ) :
    (r.mul s).zeroSet = r.zeroSet ∪ s.zeroSet := by
  ext n; simp [zeroSet, mul_eq_zero]

lemma diagonal_inv (d : ι → K) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one (n := ι) (α := K) using 2
  funext i
  exact inv_mul_cancel₀ (hd i)

lemma diagonal_zpow (d : ι → K) (hd : ∀ i, d i ≠ 0) (n : ℤ) :
    (Matrix.diagonal d) ^ n = Matrix.diagonal (fun i => d i ^ n) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [_root_.zpow_natCast, Matrix.diagonal_pow]
    congr 1
    funext i
    simp [_root_.zpow_natCast]
  · rw [Matrix.zpow_neg_natCast, Matrix.diagonal_pow,
      diagonal_inv (d ^ m) (fun i => by simpa [Pi.pow_apply] using pow_ne_zero m (hd i))]
    congr 1
    funext i
    simp [_root_.zpow_neg, _root_.zpow_natCast]

/-- The recurrence `n ↦ t^{n-b} - 1` (zero set `{b}` when `t` has infinite order). -/
def single (t : K) (ht : t ≠ 0) (b : ℤ) : LinRepZ K (Fin 2) :=
  ⟨Matrix.diagonal ![t, 1], by simp [Matrix.det_diagonal, ht], ![t ^ (-b), -1], ![1, 1]⟩

lemma single_seq (t : K) (ht : t ≠ 0) (b n : ℤ) : (single t ht b).seq n = t ^ (n - b) - 1 := by
  simp only [seq, single]
  rw [diagonal_zpow _ (by intro i; fin_cases i <;> simp [ht])]
  simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec_diagonal, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, _root_.one_zpow, mul_one]
  rw [zpow_sub₀ ht, _root_.zpow_neg, div_eq_mul_inv]
  ring

lemma zeroSet_single (t : K) (ht : t ≠ 0) (ht' : ∀ m : ℤ, t ^ m = 1 → m = 0) (b : ℤ) :
    (single t ht b).zeroSet = {b} := by
  ext n
  simp only [zeroSet, Set.mem_setOf_eq, single_seq, sub_eq_zero, Set.mem_singleton_iff]
  constructor
  · intro h; have := ht' _ h; omega
  · rintro rfl; simp

end LinRepZ

/-- The class `𝓡` of integer zero sets of fundamental bi-infinite recurrences over `K`
(`𝓡_p = RClass (RatFunc (ZMod p))` in the paper). -/
def RClass (K : Type u) [Field K] : Set (Set ℤ) :=
  {B | ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (r : LinRepZ K ι), r.zeroSet = B}

namespace RClass

/-- Lemma 2.3: `∅ ∈ 𝓡`. -/
theorem empty_mem : (∅ : Set ℤ) ∈ RClass K :=
  ⟨Unit, inferInstance, inferInstance, LinRepZ.const 1, by ext n; simp [LinRepZ.zeroSet]⟩

/-- Lemma 2.3: `ℤ ∈ 𝓡`. -/
theorem univ_mem : (Set.univ : Set ℤ) ∈ RClass K :=
  ⟨Unit, inferInstance, inferInstance, LinRepZ.const 0, by ext n; simp [LinRepZ.zeroSet]⟩

/-- Lemma 2.3: singletons, given an element of infinite multiplicative order. -/
theorem singleton_mem (t : K) (ht : t ≠ 0) (ht' : ∀ m : ℤ, t ^ m = 1 → m = 0) (b : ℤ) :
    ({b} : Set ℤ) ∈ RClass K :=
  ⟨Fin 2, inferInstance, inferInstance, LinRepZ.single t ht b, LinRepZ.zeroSet_single t ht ht' b⟩

/-- Lemma 2.3: finite unions. -/
theorem union_mem {B C : Set ℤ} (hB : B ∈ RClass K) (hC : C ∈ RClass K) : B ∪ C ∈ RClass K := by
  obtain ⟨ι, _, _, r, rfl⟩ := hB
  obtain ⟨κ, _, _, s, rfl⟩ := hC
  exact ⟨ι × κ, inferInstance, inferInstance, r.mul s, LinRepZ.zeroSet_mul r s⟩

/-- Lemma 2.3: integer translations `B ↦ B - b = {n | n + b ∈ B}`. -/
theorem shift_mem {B : Set ℤ} (hB : B ∈ RClass K) (b : ℤ) : {n | n + b ∈ B} ∈ RClass K := by
  obtain ⟨ι, _, _, r, rfl⟩ := hB
  exact ⟨ι, inferInstance, inferInstance, r.shift b, by ext n; simp [LinRepZ.zeroSet]⟩

/-- Lemma 2.3: preimages under `n ↦ a n + b`. -/
theorem affine_preimage_mem {B : Set ℤ} (hB : B ∈ RClass K) (a b : ℤ) :
    {n | a * n + b ∈ B} ∈ RClass K := by
  obtain ⟨ι, _, _, r, rfl⟩ := hB
  exact ⟨ι, inferInstance, inferInstance, r.affine a b, by ext n; simp [LinRepZ.zeroSet]⟩

/-- Restriction to `ℕ`: the indicator-type sequence is a one-sided linear recurrence sequence. -/
theorem exists_isLinRecSeq {B : Set ℤ} (hB : B ∈ RClass K) :
    ∃ u : ℕ → K, IsLinRecSeq u ∧ ∀ n : ℕ, u n = 0 ↔ (n : ℤ) ∈ B := by
  obtain ⟨ι, _, _, r, rfl⟩ := hB
  exact ⟨fun n => r.seq n, ⟨ι, inferInstance, inferInstance, r.toLinRep,
    funext (fun n => LinRepZ.toLinRep_seq r n)⟩, fun n => Iff.rfl⟩

end RClass

/-! ### The transcendental `t = X` of `F(t)` has infinite order -/

theorem RatFunc.X_zpow_eq_one_iff {F : Type*} [Field F] (m : ℤ) :
    (RatFunc.X : RatFunc F) ^ m = 1 → m = 0 := by
  intro h
  have hX : (RatFunc.X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
  -- `X ^ k ≠ 1` for `k ≥ 1`
  have hpow : ∀ k : ℕ, 0 < k → (RatFunc.X : RatFunc F) ^ k ≠ 1 := by
    intro k hk h1
    have h2 : algebraMap (Polynomial F) (RatFunc F) (Polynomial.X ^ k) =
        algebraMap (Polynomial F) (RatFunc F) 1 := by
      rw [map_pow, RatFunc.algebraMap_X, h1, map_one]
    have h3 := IsFractionRing.injective (Polynomial F) (RatFunc F) h2
    have h4 := congrArg Polynomial.natDegree h3
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_one] at h4
    omega
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rfl
    · exact absurd (by rw [← _root_.zpow_natCast]; exact h) (hpow k hk)
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rfl
    · exfalso
      rw [_root_.zpow_neg, inv_eq_one, _root_.zpow_natCast] at h
      exact hpow k hk h

/-- Lemma 2.3 over `F(t)`: singletons lie in `𝓡`. -/
theorem RClass.singleton_mem_ratFunc {F : Type*} [Field F] (b : ℤ) :
    ({b} : Set ℤ) ∈ RClass (RatFunc F) :=
  RClass.singleton_mem RatFunc.X RatFunc.X_ne_zero (RatFunc.X_zpow_eq_one_iff) b

end ArithDyn.Derksen

/-! ### Block sums and scalar multiples of bi-infinite representations -/

namespace ArithDyn.Derksen

open Matrix

universe v

variable {K : Type v} [Field K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

namespace LinRepZ

lemma fromBlocks_inv (A : Matrix ι ι K) (D : Matrix κ κ K) (hA : IsUnit A.det) (hD : IsUnit D.det) :
    (Matrix.fromBlocks A 0 0 D)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 D⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.nonsing_inv_mul _ hA, Matrix.nonsing_inv_mul _ hD, Matrix.fromBlocks_one]

lemma fromBlocks_zpow (A : Matrix ι ι K) (D : Matrix κ κ K) (hA : IsUnit A.det) (hD : IsUnit D.det)
    (n : ℤ) : (Matrix.fromBlocks A 0 0 D) ^ n = Matrix.fromBlocks (A ^ n) 0 0 (D ^ n) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [_root_.zpow_natCast, _root_.zpow_natCast, _root_.zpow_natCast,
      Matrix.fromBlocks_diagonal_pow]
  · rw [Matrix.zpow_neg_natCast, Matrix.zpow_neg_natCast, Matrix.zpow_neg_natCast,
      Matrix.fromBlocks_diagonal_pow]
    exact fromBlocks_inv _ _ (isUnit_det_pow A hA m) (isUnit_det_pow D hD m)

/-- Block sum. -/
noncomputable def add (r : LinRepZ K ι) (s : LinRepZ K κ) : LinRepZ K (ι ⊕ κ) :=
  ⟨Matrix.fromBlocks r.A 0 0 s.A, by rw [Matrix.det_fromBlocks_zero₂₁]; exact r.hA.mul s.hA,
    Sum.elim r.ℓ s.ℓ, Sum.elim r.v s.v⟩

@[simp] lemma add_seq (r : LinRepZ K ι) (s : LinRepZ K κ) (n : ℤ) :
    (r.add s).seq n = r.seq n + s.seq n := by
  simp only [seq, add]
  rw [fromBlocks_zpow _ _ r.hA s.hA, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, add_zero, zero_add,
    sumElim_dotProduct_sumElim]

/-- Scalar multiple. -/
noncomputable def smul (c : K) (r : LinRepZ K ι) : LinRepZ K ι := ⟨r.A, r.hA, c • r.ℓ, r.v⟩

@[simp] lemma smul_seq (c : K) (r : LinRepZ K ι) (n : ℤ) : (smul c r).seq n = c * r.seq n := by
  simp only [seq, smul, smul_dotProduct, smul_eq_mul]

end LinRepZ

end ArithDyn.Derksen
