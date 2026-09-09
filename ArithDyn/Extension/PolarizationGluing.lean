import ArithDyn.Extension.PolarizationPowers

/-!
# Polarization powers across arbitrary original covers

All cross-chart multipliers come from one original sheaf isomorphism.  Actual
sheaf gluing removes any requirement that one cover refine the other.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace Opposite
open ArithDyn.Extension.SectionAlgebra

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{max u v}} {ι : Type v} (C D : UnitCocycle X ι) (d : ℕ)
variable (μ : twistedModule C 1 ≅ twistedModule D d)

def crossPowerCoefficient {n : ℕ} {V : X.Opens} (a : TwistedSections C n V)
    (i j : ι) (W : X.Opens) (hW : W ≤ V) (hi : W ≤ C.cover i)
    (hj : W ≤ D.cover j) : Γ(X, W) :=
  (polarizationUnit C D d μ i j W hi hj : Γ(X, W)) ^ n *
    chartCoefficient C a i W hW hi

theorem crossPowerCoefficient_restrict {n : ℕ} {V W Z : X.Opens}
    (a : TwistedSections C n V) (i j : ι) (hZW : Z ≤ W) (hWV : W ≤ V)
    (hi : W ≤ C.cover i) (hj : W ≤ D.cover j) :
    res hZW (crossPowerCoefficient C D d μ a i j W hWV hi hj) =
      crossPowerCoefficient C D d μ a i j Z (hZW.trans hWV)
        (hZW.trans hi) (hZW.trans hj) := by
  unfold crossPowerCoefficient
  rw [map_mul, map_pow, chartCoefficient_restrict]
  have hu := congrArg (fun z : Γ(X, Z)ˣ => (z : Γ(X, Z)))
    (polarizationUnit_naturality C D d μ i j hZW hi hj)
  rw [show res hZW (polarizationUnit C D d μ i j W hi hj : Γ(X, W)) =
    (polarizationUnit C D d μ i j Z _ _ : Γ(X, Z)) from hu]

/-- The single degree-one gauge identity controls every pair of future degrees. -/
theorem crossPowerCoefficient_change {n : ℕ} {V : X.Opens}
    (a : TwistedSections C n V) (i j k l : ι) (W : X.Opens)
    (hW : W ≤ V) (hi : W ≤ C.cover i) (hj : W ≤ D.cover j)
    (hk : W ≤ C.cover k) (hl : W ≤ D.cover l) :
    crossPowerCoefficient C D d μ a i j W hW hi hj =
      (D.g j l W hj hl : Γ(X, W)) ^ (d * n) *
        crossPowerCoefficient C D d μ a k l W hW hk hl := by
  unfold crossPowerCoefficient
  rw [chartCoefficient_change C a i k W hW hi hk]
  have hu := congrArg (fun z : Γ(X, W) => z ^ n)
    (polarizationUnit_overlap C D d μ i j k l W hi hj hk hl)
  dsimp only at hu
  rw [mul_pow, mul_pow, ← pow_mul] at hu
  rw [← mul_assoc, hu, mul_assoc]

/-- On one source chart all target-chart coefficients are already retained. -/
def powerOnSource {n : ℕ} {V : X.Opens} (a : TwistedSections C n V)
    (i : ι) (W : X.Opens) (hW : W ≤ V) (hi : W ≤ C.cover i) :
    TwistedSections D (d * n) W := by
  refine ⟨fun j => crossPowerCoefficient C D d μ a i j (W ⊓ D.cover j)
    (inf_le_left.trans hW) (inf_le_left.trans hi) inf_le_right, ?_⟩
  intro j l
  rw [crossPowerCoefficient_restrict, crossPowerCoefficient_restrict]
  exact crossPowerCoefficient_change C D d μ a i j i l
    (overlap D W j l) ((inf_le_left.trans inf_le_left).trans hW)
    ((inf_le_left.trans inf_le_left).trans hi)
    (inf_le_left.trans inf_le_right) ((inf_le_left.trans inf_le_left).trans hi) inf_le_right

@[simp] theorem powerOnSource_apply {n : ℕ} {V : X.Opens}
    (a : TwistedSections C n V) (i j : ι) (W : X.Opens)
    (hW : W ≤ V) (hi : W ≤ C.cover i) :
    (powerOnSource C D d μ a i W hW hi).1 j =
      crossPowerCoefficient C D d μ a i j (W ⊓ D.cover j)
        (inf_le_left.trans hW) (inf_le_left.trans hi) inf_le_right := rfl

theorem powerOnSource_restrict {n : ℕ} {V W Z : X.Opens}
    (a : TwistedSections C n V) (i : ι) (hZW : Z ≤ W) (hWV : W ≤ V)
    (hi : W ≤ C.cover i) :
    restrictSections D (d * n) hZW (powerOnSource C D d μ a i W hWV hi) =
      powerOnSource C D d μ a i Z (hZW.trans hWV) (hZW.trans hi) := by
  ext j
  exact crossPowerCoefficient_restrict C D d μ a i j
    (inf_le_inf hZW le_rfl) (inf_le_left.trans hWV) (inf_le_left.trans hi) inf_le_right

theorem powerOnSource_independent {n : ℕ} {V : X.Opens}
    (a : TwistedSections C n V) (i k : ι) (W : X.Opens)
    (hW : W ≤ V) (hi : W ≤ C.cover i) (hk : W ≤ C.cover k) :
    powerOnSource C D d μ a i W hW hi = powerOnSource C D d μ a k W hW hk := by
  ext j
  have h := crossPowerCoefficient_change C D d μ a i j k j (W ⊓ D.cover j)
    (inf_le_left.trans hW) (inf_le_left.trans hi) inf_le_right
    (inf_le_left.trans hk) inf_le_right
  simpa only [D.self, Units.val_one, one_pow, one_mul] using h

/-- The original target sheaf glues the complete family across the source cover. -/
theorem existsUnique_globalPowerSections (n : ℕ) (V : X.Opens)
    (a : TwistedSections C n V) :
    ∃! b : TwistedSections D (d * n) V,
      ∀ i, restrictSections D (d * n) inf_le_left b =
        powerOnSource C D d μ a i (V ⊓ C.cover i) inf_le_left inf_le_right := by
  have hc : V ≤ ⨆ i : ULift.{max u v} ι, V ⊓ C.cover i.down := by
    rw [← inf_iSup_eq]
    have he : (⨆ i : ULift.{max u v} ι, C.cover i.down) = ⨆ i, C.cover i := by simp
    rw [he, C.covers, inf_top_eq]
  have hs (i j : ULift.{max u v} ι) :
      restrictSections D (d * n) inf_le_left
        (powerOnSource C D d μ a i.down (V ⊓ C.cover i.down) inf_le_left inf_le_right) =
      restrictSections D (d * n) (inf_le_right :
          (V ⊓ C.cover i.down) ⊓ (V ⊓ C.cover j.down) ≤ V ⊓ C.cover j.down)
        (powerOnSource C D d μ a j.down (V ⊓ C.cover j.down) inf_le_left inf_le_right) := by
    rw [powerOnSource_restrict, powerOnSource_restrict]
    exact powerOnSource_independent C D d μ a i.down j.down _ _ _ _
  obtain ⟨b, hb, hub⟩ := existsUnique_gluingSections D (d * n)
    (fun i : ULift.{max u v} ι => V ⊓ C.cover i.down) V
    (fun _ => inf_le_left) hc
    (fun i => powerOnSource C D d μ a i.down _ inf_le_left inf_le_right) hs
  refine ⟨b, fun i => hb ⟨i⟩, ?_⟩
  intro b' hb'
  exact hub b' (fun i => hb' i.down)

/-- Full powers across arbitrary covers, constructed from one actual isomorphism. -/
def globalPowerSections (n : ℕ) (V : X.Opens) (a : TwistedSections C n V) :
    TwistedSections D (d * n) V :=
  (existsUnique_globalPowerSections C D d μ n V a).choose

/-- Every original source chart reads the same glued global power section. -/
theorem globalPowerSections_source (n : ℕ) (V : X.Opens)
    (a : TwistedSections C n V) (i : ι) :
    restrictSections D (d * n) inf_le_left (globalPowerSections C D d μ n V a) =
      powerOnSource C D d μ a i (V ⊓ C.cover i) inf_le_left inf_le_right :=
  (existsUnique_globalPowerSections C D d μ n V a).choose_spec.1 i

end ArithDyn.Extension.ProjTwist

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{max u v}} {ι : Type v} (C D : UnitCocycle X ι) (d : ℕ)
variable (μ : twistedModule C 1 ≅ twistedModule D d)

theorem globalPowerSections_on_source (n : ℕ) (V : X.Opens)
    (a : TwistedSections C n V) (i : ι) (W : X.Opens)
    (hW : W ≤ V) (hi : W ≤ C.cover i) :
    restrictSections D (d * n) hW (globalPowerSections C D d μ n V a) =
      powerOnSource C D d μ a i W hW hi := by
  have h := congrArg (restrictSections D (d * n) (le_inf hW hi))
    (globalPowerSections_source C D d μ n V a i)
  simpa only [restrictSections_comp, powerOnSource_restrict] using h

/-- On every actual intersection the global map reads the original unit power. -/
theorem globalPowerSections_coefficient (n : ℕ) (V : X.Opens)
    (a : TwistedSections C n V) (i j : ι) (W : X.Opens)
    (hW : W ≤ V) (hi : W ≤ C.cover i) (hj : W ≤ D.cover j) :
    res (le_inf hW hj) ((globalPowerSections C D d μ n V a).1 j) =
      crossPowerCoefficient C D d μ a i j W hW hi hj := by
  have h := congrArg (fun b : TwistedSections D (d * n) W =>
    toLocal D (d * n) j W hj b)
    (globalPowerSections_on_source C D d μ n V a i W hW hi)
  change res _ (res _ ((globalPowerSections C D d μ n V a).1 j)) =
    res _ (crossPowerCoefficient C D d μ a i j (W ⊓ D.cover j) _ _ _) at h
  simpa only [res_comp, crossPowerCoefficient_restrict] using h

/-- The original source cover detects equality of arbitrary regular functions. -/
theorem regular_eq_on_source_cover (V : X.Opens) (s t : Γ(X, V))
    (h : ∀ i, res (inf_le_left : V ⊓ C.cover i ≤ V) s =
      res (inf_le_left : V ⊓ C.cover i ≤ V) t) : s = t := by
  apply X.sheaf.eq_of_locally_eq' (fun i : ULift.{max u v} ι => V ⊓ C.cover i.down)
    V (fun _ => homOfLE inf_le_left)
  · rw [← inf_iSup_eq]
    have he : (⨆ i : ULift.{max u v} ι, C.cover i.down) = ⨆ i, C.cover i := by simp
    rw [he, C.covers, inf_top_eq]
  · intro i
    exact h i.down

theorem globalPowerSections_add (n : ℕ) (V : X.Opens)
    (a b : TwistedSections C n V) :
    globalPowerSections C D d μ n V (a + b) =
      globalPowerSections C D d μ n V a + globalPowerSections C D d μ n V b := by
  ext j
  apply regular_eq_on_source_cover C (V ⊓ D.cover j)
  intro i
  change res _ ((globalPowerSections C D d μ n V (a + b)).1 j) =
    res _ ((globalPowerSections C D d μ n V a).1 j +
      (globalPowerSections C D d μ n V b).1 j)
  rw [map_add]
  rw [globalPowerSections_coefficient C D d μ n V (a + b) i j _
      (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans inf_le_right),
    globalPowerSections_coefficient C D d μ n V a i j _
      (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans inf_le_right),
    globalPowerSections_coefficient C D d μ n V b i j _
      (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans inf_le_right)]
  simp only [crossPowerCoefficient, chartCoefficient, toLocal,
    restrictSections_apply, Submodule.coe_add, Pi.add_apply, map_add, mul_add]

theorem globalPowerSections_smul (n : ℕ) (V : X.Opens)
    (r : Γ(X, V)) (a : TwistedSections C n V) :
    globalPowerSections C D d μ n V (r • a) =
      r • globalPowerSections C D d μ n V a := by
  ext j
  apply regular_eq_on_source_cover C (V ⊓ D.cover j)
  intro i
  change res _ ((globalPowerSections C D d μ n V (r • a)).1 j) =
    res _ (res inf_le_left r * (globalPowerSections C D d μ n V a).1 j)
  rw [map_mul, res_comp,
    globalPowerSections_coefficient C D d μ n V (r • a) i j _
      (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans inf_le_right),
    globalPowerSections_coefficient C D d μ n V a i j _
      (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans inf_le_right)]
  change _ * res _ (res _ (res inf_le_left r * a.1 i)) =
    _ * (_ * res _ (res _ (a.1 i)))
  simp only [map_mul, res_comp]
  ring

/-- Every homogeneous map is linear over the original section ring. -/
def globalPowerLinearMap (n : ℕ) (V : X.Opens) :
    TwistedSections C n V →ₗ[Γ(X, V)] TwistedSections D (d * n) V where
  toFun := globalPowerSections C D d μ n V
  map_add' := globalPowerSections_add C D d μ n V
  map_smul' := globalPowerSections_smul C D d μ n V

/-- All degrees commute with every original restriction map. -/
theorem globalPowerSections_restrict (n : ℕ) {V W : X.Opens}
    (h : V ≤ W) (a : TwistedSections C n W) :
    globalPowerSections C D d μ n V (restrictSections C n h a) =
      restrictSections D (d * n) h (globalPowerSections C D d μ n W a) := by
  ext j
  apply regular_eq_on_source_cover C (V ⊓ D.cover j)
  intro i
  change res _ ((globalPowerSections C D d μ n V (restrictSections C n h a)).1 j) =
    res _ (res _ ((globalPowerSections C D d μ n W a).1 j))
  rw [res_comp,
    globalPowerSections_coefficient C D d μ n V (restrictSections C n h a) i j _
      (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans inf_le_right),
    globalPowerSections_coefficient C D d μ n W a i j _
      ((inf_le_left.trans inf_le_left).trans h) inf_le_right (inf_le_left.trans inf_le_right)]
  unfold crossPowerCoefficient chartCoefficient
  rw [restrictSections_comp]

/-- One unit raised to all powers preserves the complete graded multiplication. -/
theorem globalPowerSections_mul_apply {n m : ℕ} {V : X.Opens}
    (a : TwistedSections C n V) (b : TwistedSections C m V) (j : ι) :
    (globalPowerSections C D d μ (n + m) V (mulSections C a b)).1 j =
      (globalPowerSections C D d μ n V a).1 j *
        (globalPowerSections C D d μ m V b).1 j := by
  apply regular_eq_on_source_cover C (V ⊓ D.cover j)
  intro i
  rw [map_mul,
    globalPowerSections_coefficient C D d μ (n + m) V (mulSections C a b) i j _
      (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans inf_le_right),
    globalPowerSections_coefficient C D d μ n V a i j _
      (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans inf_le_right),
    globalPowerSections_coefficient C D d μ m V b i j _
      (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans inf_le_right)]
  simp only [crossPowerCoefficient, chartCoefficient, toLocal,
    restrictSections_apply, mulSections_apply, map_mul, pow_add]
  ring

/-- Degree zero preserves the actual multiplicative unit. -/
theorem globalPowerSections_zero_one_apply (V : X.Opens) (j : ι) :
    (globalPowerSections C D d μ 0 V ⟨1, compatible_one C V⟩).1 j = 1 := by
  apply regular_eq_on_source_cover C (V ⊓ D.cover j)
  intro i
  rw [map_one,
    globalPowerSections_coefficient C D d μ 0 V _ i j _
      (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans inf_le_right)]
  simp only [crossPowerCoefficient, chartCoefficient, toLocal,
    restrictSections_apply, pow_zero, one_mul]
  change res _ (res _ 1) = 1
  rw [map_one, map_one]

/-- Degree one recovers the given original isomorphism on every section. -/
theorem globalPowerSections_one_apply (V : X.Opens)
    (a : TwistedSections C 1 V) (j : ι) :
    (globalPowerSections C D d μ 1 V a).1 j =
      (polarizationSectionEquiv C D d μ V a).1 j := by
  apply regular_eq_on_source_cover C (V ⊓ D.cover j)
  intro i
  rw [globalPowerSections_coefficient C D d μ 1 V a i j _
    (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans inf_le_right)]
  unfold crossPowerCoefficient chartCoefficient
  rw [pow_one, ← polarizationUnit_action, polarizationSectionEquiv_restrict]
  change res _ (res _ ((polarizationSectionEquiv C D d μ V a).1 j)) = _
  rw [res_comp]

end ArithDyn.Extension.ProjTwist
