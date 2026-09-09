import Mathlib

/-!
# The cubic plane map `f[A:B:Z] = [A R : B R : A² Z]`, `R = B(A+Z) - AZ` (paper §4, (4.3))

We model `ℙ²(K)` as `ℙ K (Fin 3 → K)` (Mathlib's `Projectivization`).

* `Fvec v` is the vector of the three cubic forms evaluated at `v`;
* `Indet P` is the indeterminacy predicate (all three forms vanish at a representative);
* `fstep : ℙ² → Option ℙ²` is the map as a partial function (`none` on `I(f)`);
* `orbit P n` is the `n`-th step of the forward orbit computed step by step from the
  original map (Definition 4.1), and `TotallyDefined P` says that every step is defined.

We prove Lemma 4.3 (first part: `I(f) = {O, E, F}`), the chart formula of Lemma 4.4
(`fstep (Φ u v) = Φ u (uv)`), and the orbit criterion
`TotallyDefined (Φ u v) ↔ ∀ n, uⁿ v ≠ 1`.
-/

set_option autoImplicit false

namespace ArithDyn.Density

open Projectivization

variable {K : Type*} [Field K]

/-- The projective plane over `K`. -/
abbrev P2 (K : Type*) [Field K] := Projectivization K (Fin 3 → K)

/-- `R(A,B,Z) = B(A+Z) - AZ` (4.3). -/
def Rq (v : Fin 3 → K) : K := v 1 * (v 0 + v 2) - v 0 * v 2

/-- The three cubic coordinates `(A R, B R, A² Z)` of `f` (4.3). -/
def Fvec (v : Fin 3 → K) : Fin 3 → K := ![v 0 * Rq v, v 1 * Rq v, v 0 ^ 2 * v 2]

lemma Rq_smul (c : K) (v : Fin 3 → K) : Rq (c • v) = c ^ 2 * Rq v := by
  simp only [Rq, Pi.smul_apply, smul_eq_mul]; ring

lemma Fvec_smul (c : K) (v : Fin 3 → K) : Fvec (c • v) = c ^ 3 • Fvec v := by
  ext i; fin_cases i <;> simp [Fvec, Rq_smul] <;> ring

/-- The common zero set of the three cubic forms. -/
lemma Fvec_eq_zero_iff (v : Fin 3 → K) :
    Fvec v = 0 ↔ (v 0 = 0 ∧ v 1 = 0) ∨ (v 0 = 0 ∧ v 2 = 0) ∨ (v 1 = 0 ∧ v 2 = 0) := by
  constructor
  · intro h
    have e0 : v 0 * Rq v = 0 := by simpa [Fvec] using congrFun h 0
    have e1 : v 1 * Rq v = 0 := by simpa [Fvec] using congrFun h 1
    have e2 : v 0 ^ 2 * v 2 = 0 := by simpa [Fvec] using congrFun h 2
    rcases mul_eq_zero.1 e2 with h0 | h2
    · have h0 : v 0 = 0 := by simpa using h0
      have hR : Rq v = v 1 * v 2 := by simp [Rq, h0]
      rw [hR] at e1
      rcases mul_eq_zero.1 e1 with h1 | h12
      · exact Or.inl ⟨h0, h1⟩
      · rcases mul_eq_zero.1 h12 with h1 | h2
        · exact Or.inl ⟨h0, h1⟩
        · exact Or.inr (Or.inl ⟨h0, h2⟩)
    · have hR : Rq v = v 1 * v 0 := by simp [Rq, h2]
      rw [hR] at e0
      rcases mul_eq_zero.1 e0 with h0 | h10
      · exact Or.inr (Or.inl ⟨h0, h2⟩)
      · rcases mul_eq_zero.1 h10 with h1 | h0
        · exact Or.inr (Or.inr ⟨h1, h2⟩)
        · exact Or.inr (Or.inl ⟨h0, h2⟩)
  · rintro (⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩) <;> ext i <;> fin_cases i <;> simp [Fvec, Rq, *]

/-! ### The three special points -/

lemma vO_ne : (![0, 0, 1] : Fin 3 → K) ≠ 0 := by
  intro h; have := congrFun h 2; simp at this

lemma vE_ne : (![0, 1, 0] : Fin 3 → K) ≠ 0 := by
  intro h; have := congrFun h 1; simp at this

lemma vF_ne : (![1, 0, 0] : Fin 3 → K) ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

/-- `O = [0:0:1]`. -/
def O : P2 K := mk K ![0, 0, 1] vO_ne
/-- `E = [0:1:0]`. -/
def E : P2 K := mk K ![0, 1, 0] vE_ne
/-- `F = [1:0:0]`. -/
def F : P2 K := mk K ![1, 0, 0] vF_ne

/-! ### Indeterminacy and the one-step map -/

/-- The indeterminacy predicate: all three cubic forms vanish (at the chosen representative,
which does not matter by homogeneity). -/
def Indet (P : P2 K) : Prop := Fvec P.rep = 0

lemma Fvec_rep_mk (v : Fin 3 → K) (hv : v ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ Fvec (mk K v hv).rep = c • Fvec v := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv
  refine ⟨(a : K) ^ 3, pow_ne_zero _ a.ne_zero, ?_⟩
  rw [← ha, Units.smul_def, Fvec_smul]

lemma indet_mk (v : Fin 3 → K) (hv : v ≠ 0) : Indet (mk K v hv) ↔ Fvec v = 0 := by
  obtain ⟨c, hc, h⟩ := Fvec_rep_mk v hv
  unfold Indet
  rw [h, smul_eq_zero]
  simp [hc]

lemma indet_O : Indet (O : P2 K) := by
  rw [O, indet_mk, Fvec_eq_zero_iff]; simp

lemma indet_E : Indet (E : P2 K) := by
  rw [E, indet_mk, Fvec_eq_zero_iff]; simp

lemma indet_F : Indet (F : P2 K) := by
  rw [F, indet_mk, Fvec_eq_zero_iff]; simp

/-- Lemma 4.3 (first part): the indeterminacy locus is exactly `{O, E, F}` (4.5). -/
theorem indet_iff (P : P2 K) : Indet P ↔ P = O ∨ P = E ∨ P = F := by
  induction P using Projectivization.ind with
  | h v hv =>
    rw [indet_mk, Fvec_eq_zero_iff]
    constructor
    · rintro (⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩)
      · left
        rw [O, mk_eq_mk_iff']
        exact ⟨v 2, by ext i; fin_cases i <;> simp [h0, h1]⟩
      · right; left
        rw [E, mk_eq_mk_iff']
        exact ⟨v 1, by ext i; fin_cases i <;> simp [h0, h2]⟩
      · right; right
        rw [F, mk_eq_mk_iff']
        exact ⟨v 0, by ext i; fin_cases i <;> simp [h1, h2]⟩
    · rintro (h | h | h)
      · have := indet_O (K := K); rw [← h, indet_mk, Fvec_eq_zero_iff] at this; exact this
      · have := indet_E (K := K); rw [← h, indet_mk, Fvec_eq_zero_iff] at this; exact this
      · have := indet_F (K := K); rw [← h, indet_mk, Fvec_eq_zero_iff] at this; exact this

/-- `(some a).bind f = f a` (definitional). -/
@[simp] lemma some_bind {α β : Type*} (a : α) (f : α → Option β) : (some a).bind f = f a := rfl

open scoped Classical in
/-- One step of the map, as a partial function (`none` exactly on `I(f)`). -/
noncomputable def fstep (P : P2 K) : Option (P2 K) :=
  if h : Fvec P.rep = 0 then none else some (mk K (Fvec P.rep) h)

lemma fstep_eq_none_iff (P : P2 K) : fstep P = none ↔ Indet P := by
  unfold fstep Indet
  split_ifs with h <;> simp [h]

lemma fstep_mk (v : Fin 3 → K) (hv : v ≠ 0) (hF : Fvec v ≠ 0) :
    fstep (mk K v hv) = some (mk K (Fvec v) hF) := by
  obtain ⟨c, hc, h⟩ := Fvec_rep_mk v hv
  have hne : Fvec (mk K v hv).rep ≠ 0 := by rw [h]; exact smul_ne_zero hc hF
  unfold fstep
  rw [dif_neg hne]
  congr 1
  rw [mk_eq_mk_iff']
  exact ⟨c, h.symm⟩

/-- The value of `f` at a point of its domain. -/
noncomputable def fmap (P : P2 K) (h : ¬ Indet P) : P2 K := mk K (Fvec P.rep) h

lemma fstep_of_not_indet (P : P2 K) (h : ¬ Indet P) : fstep P = some (fmap P h) := by
  unfold fstep fmap
  exact dif_neg h

/-! ### Orbits and the totally defined locus (Definition 4.1) -/

/-- `orbit P n = some Pₙ` when `P₀, …, Pₙ₋₁ ∉ I(f)`, and `none` once the orbit has hit `I(f)`. -/
noncomputable def orbit (P : P2 K) : ℕ → Option (P2 K)
  | 0 => some P
  | n + 1 => (orbit P n).bind fstep

/-- Definition 4.1: `P ∈ ℙ²(K)_f` iff all iterates `P_j` are defined and lie outside `I(f)`,
i.e. iff no step of the orbit is `none`. -/
def TotallyDefined (P : P2 K) : Prop := ∀ n, orbit P n ≠ none

@[simp] lemma orbit_zero (P : P2 K) : orbit P 0 = some P := rfl

lemma orbit_succ (P : P2 K) (n : ℕ) : orbit P (n + 1) = (orbit P n).bind fstep := rfl

lemma orbit_succ' (P : P2 K) (n : ℕ) :
    orbit P (n + 1) = (fstep P).bind (fun Q => orbit Q n) := by
  induction n with
  | zero =>
    rw [orbit_succ, orbit_zero, some_bind]
    cases fstep P <;> rfl
  | succ n ih =>
    rw [orbit_succ, ih]
    cases fstep P with
    | none => rfl
    | some Q => rfl

lemma not_totallyDefined_of_indet {P : P2 K} (h : Indet P) : ¬ TotallyDefined P := by
  intro hT
  apply hT 1
  rw [orbit_succ, orbit_zero, some_bind, fstep_eq_none_iff]
  exact h

/-- The sets `D_m` of Definition 4.1: `D₀ = ℙ² \ I(f)`, `D_{m+1} = {P ∈ D₀ : f(P) ∈ D_m}`. -/
def D : ℕ → Set (P2 K)
  | 0 => {P | ¬ Indet P}
  | m + 1 => {P | ∃ h : ¬ Indet P, fmap P h ∈ D m}

lemma mem_D_iff (m : ℕ) (P : P2 K) : P ∈ D m ↔ orbit P (m + 1) ≠ none := by
  induction m generalizing P with
  | zero =>
    show ¬ Indet P ↔ _
    rw [orbit_succ, orbit_zero, some_bind, Ne, fstep_eq_none_iff]
  | succ m ih =>
    show (∃ h : ¬ Indet P, fmap P h ∈ D m) ↔ _
    rw [orbit_succ' P (m + 1)]
    by_cases h : Indet P
    · rw [(fstep_eq_none_iff P).2 h]
      simp [h]
    · rw [fstep_of_not_indet P h, some_bind]
      simp only [h, not_false_eq_true, exists_true_left]
      exact ih _

/-- Definition 4.1, second form: `ℙ²(K)_f = ⋂ₘ D_m`. -/
theorem totallyDefined_iff_forall_mem_D (P : P2 K) : TotallyDefined P ↔ ∀ m, P ∈ D m := by
  constructor
  · intro h m
    rw [mem_D_iff]
    exact h (m + 1)
  · intro h n
    cases n with
    | zero => simp
    | succ m => exact (mem_D_iff m P).1 (h m)

/-! ### The affine chart `Φ(u,v) = [v-1 : u(v-1) : 1]` (4.9) and Lemma 4.4 -/

lemma vPhi_ne (u v : K) : (![v - 1, u * (v - 1), 1] : Fin 3 → K) ≠ 0 := by
  intro h; have := congrFun h 2; simp at this

/-- `Φ(u,v) = [v-1 : u(v-1) : 1]` (4.9). -/
def Phi (u v : K) : P2 K := mk K ![v - 1, u * (v - 1), 1] (vPhi_ne u v)

lemma Phi_one (u : K) : Phi u 1 = O := by
  rw [Phi, O, mk_eq_mk_iff']
  exact ⟨1, by ext i; fin_cases i <;> simp⟩

lemma indet_Phi_iff (u v : K) : Indet (Phi u v) ↔ v = 1 := by
  rw [Phi, indet_mk, Fvec_eq_zero_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, one_ne_zero, and_false, or_false, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h; exact ⟨h, Or.inr h⟩

lemma Fvec_Phi (u v : K) :
    Fvec ![v - 1, u * (v - 1), 1] = (v - 1) ^ 2 • ![u * v - 1, u * (u * v - 1), 1] := by
  ext i; fin_cases i <;> simp [Fvec, Rq] <;> ring

/-- Lemma 4.4, one step: for `v ≠ 1`, `f(Φ(u,v)) = Φ(u, uv)` (4.10); note `Φ(u,1) = O`. -/
lemma fstep_Phi {u v : K} (hv : v ≠ 1) : fstep (Phi u v) = some (Phi u (u * v)) := by
  have hne : Fvec ![v - 1, u * (v - 1), 1] ≠ 0 := by
    rw [Fvec_Phi]
    exact smul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hv)) (vPhi_ne u (u * v))
  rw [Phi, fstep_mk _ _ hne]
  congr 1
  rw [Phi, mk_eq_mk_iff']
  exact ⟨(v - 1) ^ 2, (Fvec_Phi u v).symm⟩

/-- Lemma 4.4, iterated (4.11): as long as `uⁱ v ≠ 1` for `i < n`, `P_n = Φ(u, uⁿ v)`. -/
lemma orbit_Phi {u v : K} (n : ℕ) (h : ∀ i < n, u ^ i * v ≠ 1) :
    orbit (Phi u v) n = some (Phi u (u ^ n * v)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orbit_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), some_bind,
      fstep_Phi (h n (Nat.lt_succ_self n))]
    congr 2
    ring

/-- The orbit criterion in the chart: for `v ≠ 1`,
`Φ(u,v) ∈ ℙ²(K)_f ↔ ∀ n, uⁿ v ≠ 1` (cf. (4.14)). -/
theorem totallyDefined_Phi_iff {u v : K} (hv : v ≠ 1) :
    TotallyDefined (Phi u v) ↔ ∀ n, u ^ n * v ≠ 1 := by
  classical
  constructor
  · intro hT n hn
    have hex : ∃ n, u ^ n * v = 1 := ⟨n, hn⟩
    have hm : u ^ Nat.find hex * v = 1 := Nat.find_spec hex
    have hlt : ∀ i < Nat.find hex, u ^ i * v ≠ 1 := fun i hi => Nat.find_min hex hi
    have h1 : orbit (Phi u v) (Nat.find hex) = some (Phi u (u ^ Nat.find hex * v)) :=
      orbit_Phi _ hlt
    rw [hm, Phi_one] at h1
    apply hT (Nat.find hex + 1)
    rw [orbit_succ, h1, some_bind, fstep_eq_none_iff]
    exact indet_O
  · intro h n
    rw [orbit_Phi n (fun i _ => h i)]
    exact Option.some_ne_none _

/-! ### Normal forms of points -/

lemma vab_ne (a b : K) : (![a, b, 1] : Fin 3 → K) ≠ 0 := by
  intro h; have := congrFun h 2; simp at this

lemma va_ne (a : K) : (![a, 1, 0] : Fin 3 → K) ≠ 0 := by
  intro h; have := congrFun h 1; simp at this

/-- The affine chart point `[a : b : 1]`. -/
def aff (a b : K) : P2 K := mk K ![a, b, 1] (vab_ne a b)

/-- The point `[a : 1 : 0]` on the line at infinity. -/
def inf (a : K) : P2 K := mk K ![a, 1, 0] (va_ne a)

lemma inf_zero : inf (0 : K) = E := rfl

lemma aff_eq_aff_iff {a b a' b' : K} : aff a b = aff a' b' ↔ a = a' ∧ b = b' := by
  rw [aff, aff, mk_eq_mk_iff']
  constructor
  · rintro ⟨c, hc⟩
    have h2 : c = 1 := by simpa using congrFun hc 2
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp [h2] at h0 h1
    exact ⟨h0.symm, h1.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨1, by simp⟩

lemma inf_eq_inf_iff {a a' : K} : inf a = inf a' ↔ a = a' := by
  rw [inf, inf, mk_eq_mk_iff']
  constructor
  · rintro ⟨c, hc⟩
    have h1 : c = 1 := by simpa using congrFun hc 1
    have h0 := congrFun hc 0
    simp [h1] at h0
    exact h0.symm
  · rintro rfl
    exact ⟨1, by simp⟩

lemma aff_ne_inf (a b a' : K) : aff a b ≠ inf a' := by
  rw [aff, inf, Ne, mk_eq_mk_iff']
  rintro ⟨c, hc⟩
  have := congrFun hc 2
  simp at this

lemma aff_ne_F (a b : K) : aff a b ≠ F := by
  rw [aff, F, Ne, mk_eq_mk_iff']
  rintro ⟨c, hc⟩
  have := congrFun hc 2
  simp at this

lemma inf_ne_F (a : K) : inf a ≠ F := by
  rw [inf, F, Ne, mk_eq_mk_iff']
  rintro ⟨c, hc⟩
  have := congrFun hc 1
  simp at this

lemma aff_zero_zero : aff (0 : K) 0 = O := rfl

/-- Every point of `ℙ²(K)` is `[a:b:1]`, `[a:1:0]`, or `F = [1:0:0]`. -/
lemma exists_normal_form (P : P2 K) :
    (∃ a b, P = aff a b) ∨ (∃ a, P = inf a) ∨ P = F := by
  induction P using Projectivization.ind with
  | h v hv =>
    by_cases h2 : v 2 = 0
    · by_cases h1 : v 1 = 0
      · right; right
        have h0 : v 0 ≠ 0 := by
          intro h0; apply hv; ext i; fin_cases i <;> simp [h0, h1, h2]
        rw [F, mk_eq_mk_iff']
        exact ⟨v 0, by ext i; fin_cases i <;> simp [h1, h2]⟩
      · right; left
        refine ⟨v 0 / v 1, ?_⟩
        rw [inf, mk_eq_mk_iff']
        refine ⟨v 1, ?_⟩
        ext i; fin_cases i <;> simp [h2]
        field_simp
    · left
      refine ⟨v 0 / v 2, v 1 / v 2, ?_⟩
      rw [aff, mk_eq_mk_iff']
      refine ⟨v 2, ?_⟩
      ext i; fin_cases i <;> simp <;> field_simp

/-- For `a ≠ 0`, `[a:b:1] = Φ(b/a, a+1)` (the coordinates (4.9)). -/
lemma aff_eq_Phi {a : K} (ha : a ≠ 0) (b : K) : aff a b = Phi (b / a) (a + 1) := by
  rw [aff, Phi, mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  ext i; fin_cases i <;> simp
  field_simp

/-! ### Behaviour on the boundary lines -/

lemma Fvec_aff_zero (b : K) : Fvec ![0, b, 1] = b ^ 2 • ![0, 1, 0] := by
  ext i; fin_cases i <;> simp [Fvec, Rq] <;> ring

/-- Points `[0:b:1]` with `b ≠ 0` map to `E` in one step. -/
lemma fstep_aff_zero {b : K} (hb : b ≠ 0) : fstep (aff 0 b) = some E := by
  have hne : Fvec ![0, b, 1] ≠ 0 := by
    rw [Fvec_aff_zero]; exact smul_ne_zero (pow_ne_zero _ hb) vE_ne
  rw [aff, fstep_mk _ _ hne]
  congr 1
  rw [E, mk_eq_mk_iff']
  exact ⟨b ^ 2, (Fvec_aff_zero b).symm⟩

lemma not_totallyDefined_aff_zero (b : K) : ¬ TotallyDefined (aff 0 b) := by
  by_cases hb : b = 0
  · subst hb; rw [aff_zero_zero]; exact not_totallyDefined_of_indet indet_O
  · intro hT
    apply hT 2
    rw [orbit_succ, orbit_succ, orbit_zero, some_bind, fstep_aff_zero hb,
      some_bind, fstep_eq_none_iff]
    exact indet_E

lemma Fvec_inf (a : K) : Fvec ![a, 1, 0] = a • ![a, 1, 0] := by
  ext i; fin_cases i <;> simp [Fvec, Rq]

/-- Points `[a:1:0]` with `a ≠ 0` are fixed (4.16). -/
lemma fstep_inf {a : K} (ha : a ≠ 0) : fstep (inf a) = some (inf a) := by
  have hne : Fvec ![a, 1, 0] ≠ 0 := by
    rw [Fvec_inf]; exact smul_ne_zero ha (va_ne a)
  rw [inf, fstep_mk _ _ hne]
  congr 1
  rw [mk_eq_mk_iff']
  exact ⟨a, (Fvec_inf a).symm⟩

lemma orbit_inf {a : K} (ha : a ≠ 0) (n : ℕ) : orbit (inf a) n = some (inf a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [orbit_succ, ih, some_bind, fstep_inf ha]

lemma totallyDefined_inf {a : K} (ha : a ≠ 0) : TotallyDefined (inf a) := fun n => by
  rw [orbit_inf ha n]; exact Option.some_ne_none _

lemma not_totallyDefined_E : ¬ TotallyDefined (E : P2 K) := not_totallyDefined_of_indet indet_E

lemma not_totallyDefined_F : ¬ TotallyDefined (F : P2 K) := not_totallyDefined_of_indet indet_F

/-- The criterion for affine points with `a ≠ 0`. -/
theorem totallyDefined_aff_iff {a : K} (ha : a ≠ 0) (b : K) :
    TotallyDefined (aff a b) ↔ ∀ n, (b / a) ^ n * (a + 1) ≠ 1 := by
  rw [aff_eq_Phi ha b]
  exact totallyDefined_Phi_iff (by intro h; apply ha; linear_combination h)

end ArithDyn.Density
