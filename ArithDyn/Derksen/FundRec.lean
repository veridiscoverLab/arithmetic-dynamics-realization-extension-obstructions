import ArithDyn.Derksen.ZRec

/-!
# Fundamental bi-infinite recurrences: annihilator form and state form (paper §2.2)

The paper defines a *fundamental bi-infinite recurrence* `u : ℤ → K` as a sequence annihilated
by a monic polynomial with nonzero constant term, and notes that this is equivalent to the state
form `u n = ℓ Aⁿ v` with `A ∈ GL` (2.1), via companion matrices and Cayley–Hamilton. We prove
this equivalence (`isFundRec_iff_exists_rep`) and use the annihilator form to obtain the
remaining closure property of Lemma 2.3: images under `n ↦ a n + b` (interleaving), whose
annihilator is `P(Xᵃ)`.
-/

set_option autoImplicit false

namespace ArithDyn.Derksen

open Matrix Finset Polynomial

universe u

variable {K : Type u} [Field K]

/-- `u : ℤ → K` is a fundamental bi-infinite recurrence: there is a monic `P` with `P(0) ≠ 0` and
`∑ᵢ P.coeff i · u(n + i) = 0` for all `n ∈ ℤ`. -/
def IsFundRec (u : ℤ → K) : Prop :=
  ∃ P : Polynomial K, P.Monic ∧ P.coeff 0 ≠ 0 ∧
    ∀ n : ℤ, ∑ i ∈ range (P.natDegree + 1), P.coeff i * u (n + i) = 0

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- State form ⇒ annihilator form (Cayley–Hamilton; the constant term is `± det A ≠ 0`). -/
theorem isFundRec_of_rep (r : LinRepZ K ι) : IsFundRec r.seq := by
  classical
  refine ⟨r.A.charpoly, Matrix.charpoly_monic r.A, ?_, fun n => ?_⟩
  · intro h
    have := Matrix.det_eq_sign_charpoly_coeff r.A
    rw [h, mul_zero] at this
    exact r.hA.ne_zero this
  · have hCH := Matrix.aeval_self_charpoly r.A
    rw [Polynomial.aeval_eq_sum_range] at hCH
    -- `∑ᵢ cᵢ ℓ A^{n+i} v = ℓ (Aⁿ (∑ᵢ cᵢ Aⁱ)) v = 0`
    have key : ∀ i : ℕ, r.A.charpoly.coeff i * r.seq (n + i) =
        r.ℓ ⬝ᵥ (r.A ^ n *ᵥ ((r.A.charpoly.coeff i • r.A ^ i) *ᵥ r.v)) := by
      intro i
      simp only [LinRepZ.seq]
      rw [Matrix.zpow_add r.hA, _root_.zpow_natCast, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
        Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    simp only [key]
    rw [← dotProduct_sum, ← Matrix.mulVec_sum, ← Matrix.sum_mulVec, hCH]
    simp

/-- Annihilator form ⇒ state form (companion matrix; invertible since `P(0) ≠ 0`). -/
theorem exists_rep_of_isFundRec {u : ℤ → K} (h : IsFundRec u) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (r : LinRepZ K ι), r.seq = u := by
  classical
  obtain ⟨P, hmonic, hc₀, hrec⟩ := h
  set d := P.natDegree with hd
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- `P = 1`, so `u = 0`
    have h1 : P.coeff 0 = 1 := by
      have := hmonic.coeff_natDegree
      rwa [← hd, hd0] at this
    have hu : ∀ n, u n = 0 := by
      intro n
      have := hrec n
      rw [hd0, zero_add, Finset.sum_range_one, h1, one_mul] at this
      simpa using this
    refine ⟨Unit, inferInstance, inferInstance, LinRepZ.const 0, funext (fun n => ?_)⟩
    rw [LinRepZ.const_seq, hu]
  · -- the companion recurrence `u (m + d) = ∑_{i<d} (-cᵢ) u (m + i)`
    have hcd : P.coeff d = 1 := by rw [hd]; exact hmonic.coeff_natDegree
    have hfwd : ∀ m : ℤ, u (m + d) = ∑ i : Fin d, -P.coeff i * u (m + i) := by
      intro m
      have := hrec m
      rw [Finset.sum_range_succ, hcd, one_mul] at this
      rw [← Fin.sum_univ_eq_sum_range (fun i => P.coeff i * u (m + i)) d] at this
      rw [eq_neg_of_add_eq_zero_right this, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    let E : LinearRecurrence K := ⟨d, fun i => -P.coeff i⟩
    let A : Matrix (Fin d) (Fin d) K := LinearMap.toMatrix' E.tupleSucc
    have hA : ∀ x : Fin d → K, A *ᵥ x = E.tupleSucc x := fun x => LinearMap.toMatrix'_mulVec _ _
    have htup : ∀ (x : Fin d → K) (i : Fin d), E.tupleSucc x i =
        if h : (i : ℕ) + 1 < d then x ⟨i + 1, h⟩ else ∑ j : Fin d, -P.coeff j * x j := fun x i => rfl
    -- the window vectors `w m = (u m, …, u (m + d - 1))`
    let w : ℤ → Fin d → K := fun m i => u (m + i)
    have hstep : ∀ m : ℤ, A *ᵥ w m = w (m + 1) := by
      intro m
      rw [hA]
      funext i
      rw [htup]
      split_ifs with hlt
      · show u (m + ((i : ℕ) + 1 : ℕ)) = u (m + 1 + (i : ℕ))
        congr 1; push_cast; ring
      · have hi : (i : ℕ) + 1 = d := by have := i.isLt; omega
        have : m + 1 + (i : ℕ) = m + d := by rw [← hi]; push_cast; ring
        show ∑ j : Fin d, -P.coeff j * u (m + j) = u (m + 1 + (i : ℕ))
        rw [this, hfwd m]
    -- injectivity of the companion map, hence invertibility
    have hinj : ∀ x : Fin d → K, A *ᵥ x = 0 → x = 0 := by
      intro x hx
      rw [hA] at hx
      have hx' : ∀ i : Fin d, E.tupleSucc x i = 0 := fun i => by rw [hx]; rfl
      -- entries `1 … d-1` vanish
      have h1 : ∀ i : Fin d, 0 < (i : ℕ) → x i = 0 := by
        intro i hi
        have hprev : ((i : ℕ) - 1) + 1 < d := by have := i.isLt; omega
        have := hx' ⟨(i : ℕ) - 1, by omega⟩
        rw [htup, dif_pos hprev] at this
        have hi' : (⟨(i : ℕ) - 1 + 1, hprev⟩ : Fin d) = i := Fin.ext (by simp; omega)
        rwa [hi'] at this
      -- the last entry gives `c₀ x₀ = 0`
      have h0 : x ⟨0, hdpos⟩ = 0 := by
        have hlast := hx' ⟨d - 1, by omega⟩
        have hnot : ¬ ((d - 1 : ℕ) + 1 < d) := by omega
        rw [htup, dif_neg hnot] at hlast
        rw [Finset.sum_eq_single ⟨0, hdpos⟩] at hlast
        · simp only [Fin.val_mk, neg_mul, neg_eq_zero, mul_eq_zero] at hlast
          exact hlast.resolve_left hc₀
        · intro i _ hi
          have : 0 < (i : ℕ) := by
            rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
            · exact absurd (Fin.ext h) hi
            · exact h
          rw [h1 i this, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      funext i
      rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
      · have : i = ⟨0, hdpos⟩ := Fin.ext hi
        rw [this]; exact h0
      · exact h1 i hi
    have hunit : IsUnit A.det := by
      rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
      intro x y hxy
      have : A *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
      exact sub_eq_zero.1 (hinj _ this)
    -- `Aⁿ w m = w (m + n)` for all integers `n`
    have hpow : ∀ n : ℤ, ∀ m : ℤ, A ^ n *ᵥ w m = w (m + n) := by
      intro n
      induction n using Int.induction_on with
      | zero => intro m; simp
      | succ n ih =>
        intro m
        rw [Matrix.zpow_add_one hunit, ← Matrix.mulVec_mulVec, hstep, ih]
        congr 1; ring
      | pred n ih =>
        intro m
        have hback : A⁻¹ *ᵥ w m = w (m - 1) := by
          have hwm : w m = A *ᵥ w (m - 1) := by
            rw [hstep (m - 1)]; congr 1; ring
          rw [hwm, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
        rw [Matrix.zpow_sub_one hunit, ← Matrix.mulVec_mulVec, hback, ih]
        congr 1; ring
    refine ⟨Fin d, inferInstance, inferInstance, ⟨A, hunit, Pi.single ⟨0, hdpos⟩ 1, w 0⟩,
      funext (fun n => ?_)⟩
    simp only [LinRepZ.seq]
    rw [hpow n 0, single_dotProduct, one_mul]
    simp [w]

/-- The two definitions of "fundamental bi-infinite recurrence" agree ((2.1) in the paper). -/
theorem isFundRec_iff_exists_rep (u : ℤ → K) :
    IsFundRec u ↔ ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (r : LinRepZ K ι), r.seq = u :=
  ⟨exists_rep_of_isFundRec, fun ⟨_, _, _, r, hr⟩ => hr ▸ isFundRec_of_rep r⟩

/-- `RClass` in annihilator form. -/
theorem mem_RClass_iff (B : Set ℤ) :
    B ∈ RClass K ↔ ∃ u : ℤ → K, IsFundRec u ∧ {n | u n = 0} = B := by
  constructor
  · rintro ⟨ι, _, _, r, rfl⟩
    exact ⟨r.seq, isFundRec_of_rep r, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨ι, _, _, r, rfl⟩ := exists_rep_of_isFundRec hu
    exact ⟨ι, inferInstance, inferInstance, r, rfl⟩

/-! ### Interleaving: images under `n ↦ a n + b` -/

/-- The interleaved sequence `h(n) = u((n-b)/a)` if `a ∣ n - b`, else `0` (proof of Lemma 2.3). -/
def interleave (u : ℤ → K) (a : ℕ) (b : ℤ) (n : ℤ) : K :=
  if (a : ℤ) ∣ n - b then u ((n - b) / a) else 0

/-- `P(E)u = 0` implies `P(Eᵃ) h = 0` for the interleaved sequence `h`. -/
theorem IsFundRec.interleave {u : ℤ → K} (hu : IsFundRec u) {a : ℕ} (ha : 0 < a) (b : ℤ) :
    IsFundRec (Derksen.interleave u a b) := by
  classical
  obtain ⟨P, hmonic, hc₀, hrec⟩ := hu
  have hP0 : P ≠ 0 := hmonic.ne_zero
  refine ⟨Polynomial.expand K a P, hmonic.expand ha, ?_, fun n => ?_⟩
  · rw [Polynomial.coeff_expand ha]
    simpa using hc₀
  · rw [Polynomial.natDegree_expand]
    -- only the multiples of `a` contribute
    have hsum : ∑ i ∈ range (P.natDegree * a + 1), (Polynomial.expand K a P).coeff i *
        Derksen.interleave u a b (n + i) =
        ∑ j ∈ range (P.natDegree + 1), P.coeff j * Derksen.interleave u a b (n + a * j) := by
      simp only [Polynomial.coeff_expand ha]
      rw [← Finset.sum_filter_add_sum_filter_not (range (P.natDegree * a + 1)) (fun i => a ∣ i)]
      rw [Finset.sum_eq_zero (s := (range (P.natDegree * a + 1)).filter (fun i => ¬ a ∣ i))
        (fun i hi => by rw [if_neg (Finset.mem_filter.1 hi).2, zero_mul]), add_zero]
      -- reindex the multiples of `a`
      have himg : (range (P.natDegree * a + 1)).filter (fun i => a ∣ i) =
          (range (P.natDegree + 1)).image (fun j => a * j) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hi, j, rfl⟩
          refine ⟨j, ?_, by ring⟩
          by_contra hj
          push_neg at hj
          have : (P.natDegree + 1) * a ≤ a * j := by nlinarith
          nlinarith
        · rintro ⟨j, hj, rfl⟩
          refine ⟨?_, j, rfl⟩
          have : a * j ≤ a * P.natDegree := Nat.mul_le_mul_left a (by omega)
          nlinarith
      rw [himg, Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left ha h)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [if_pos (dvd_mul_right a j), Nat.mul_div_cancel_left j ha]
      push_cast
      rfl
    rw [hsum]
    by_cases hdvd : (a : ℤ) ∣ n - b
    · obtain ⟨m, hm⟩ := hdvd
      have hcalc : ∀ j : ℕ, Derksen.interleave u a b (n + a * j) = u (m + j) := by
        intro j
        simp only [Derksen.interleave]
        have hdiv : (a : ℤ) ∣ n + a * j - b := ⟨m + j, by rw [add_sub_right_comm, hm]; ring⟩
        rw [if_pos hdiv]
        congr 1
        rw [add_sub_right_comm, hm, ← mul_add, Int.mul_ediv_cancel_left _ (by exact_mod_cast ha.ne')]
      simp only [hcalc]
      exact hrec m
    · apply Finset.sum_eq_zero
      intro j _
      simp only [Derksen.interleave]
      have : ¬ (a : ℤ) ∣ n + a * j - b := by
        intro h
        apply hdvd
        have : n - b = (n + a * j - b) - a * j := by ring
        rw [this]
        exact dvd_sub h (dvd_mul_right _ _)
      rw [if_neg this, mul_zero]

/-- Lemma 2.3: `𝓡` is closed under images of affine maps `n ↦ a n + b` (`a ≥ 1`). -/
theorem RClass.affine_image_mem {B : Set ℤ} (hB : B ∈ RClass K) {a : ℕ} (ha : 0 < a) (b : ℤ) :
    {n | ∃ m ∈ B, n = a * m + b} ∈ RClass K := by
  classical
  obtain ⟨u, hu, rfl⟩ := (mem_RClass_iff B).1 hB
  -- `h = interleave u`, `g = 1 - interleave 1`; zero set of `h + g` is the image
  obtain ⟨ι₁, _, _, r₁, hr₁⟩ := exists_rep_of_isFundRec (hu.interleave ha b)
  obtain ⟨ι₂, _, _, r₂, hr₂⟩ :=
    exists_rep_of_isFundRec ((isFundRec_of_rep (LinRepZ.const (1 : K))).interleave ha b)
  refine ⟨ι₁ ⊕ (Unit ⊕ ι₂), inferInstance, inferInstance,
    r₁.add ((LinRepZ.const 1).add (LinRepZ.smul (-1) r₂)), ?_⟩
  ext n
  simp only [LinRepZ.zeroSet, Set.mem_setOf_eq, LinRepZ.add_seq, LinRepZ.const_seq,
    LinRepZ.smul_seq, hr₁, hr₂]
  simp only [Derksen.interleave, LinRepZ.const_seq]
  by_cases hdvd : (a : ℤ) ∣ n - b
  · simp only [if_pos hdvd]
    constructor
    · intro h
      refine ⟨(n - b) / a, by linear_combination h, ?_⟩
      rw [Int.mul_ediv_cancel' hdvd]; ring
    · rintro ⟨m, hm, rfl⟩
      have : (a * m + b - b) / a = m := by
        rw [add_sub_cancel_right, Int.mul_ediv_cancel_left _ (by exact_mod_cast ha.ne')]
      rw [this]; linear_combination hm
  · simp only [if_neg hdvd]
    constructor
    · intro h; norm_num at h
    · rintro ⟨m, _, rfl⟩
      exact absurd ⟨m, by ring⟩ hdvd

end ArithDyn.Derksen
