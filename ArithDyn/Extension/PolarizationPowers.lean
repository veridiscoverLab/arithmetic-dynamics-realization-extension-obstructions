import ArithDyn.Extension.ProjTwistReconstruction
import ArithDyn.Extension.SectionAlgebraCocycle

/-!
# All twist degrees from one actual polarization

The local multipliers are extracted from one genuine module-sheaf isomorphism.
Their compatibility is derived from its action on all sections.  No independently
chosen family of degree maps is assumed.
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

/-- Actual evaluation of the one original module-sheaf isomorphism. -/
def polarizationSectionEquiv (V : X.Opens) :
    TwistedSections C 1 V ≃ₗ[Γ(X, V)] TwistedSections D d V :=
  ((SheafOfModules.evaluation X.ringCatSheaf (op V)).mapIso μ).toLinearEquiv

@[simp] theorem polarizationSectionEquiv_apply (V : X.Opens)
    (a : TwistedSections C 1 V) :
    polarizationSectionEquiv C D d μ V a = Modules.Hom.app μ.hom V a := rfl

theorem polarizationSectionEquiv_restrict {V W : X.Opens} (h : V ≤ W)
    (a : TwistedSections C 1 W) :
    polarizationSectionEquiv C D d μ V (restrictSections C 1 h a) =
      restrictSections D d h (polarizationSectionEquiv C D d μ W a) := by
  exact congrArg (fun α => α a)
    ((Modules.Hom.mapPresheaf (X := X) μ.hom).naturality (homOfLE h).op)

/-- The local scalar automorphism in a pair of original frames. -/
def polarizationLocalEquiv (i j : ι) (V : X.Opens)
    (hi : V ≤ C.cover i) (hj : V ≤ D.cover j) : Γ(X, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  (localLinearEquiv C 1 i V hi).symm.trans
    ((polarizationSectionEquiv C D d μ V).trans (localLinearEquiv D d j V hj))

/-- The unit comes from the original isomorphism, rather than being extra input. -/
def polarizationUnit (i j : ι) (V : X.Opens)
    (hi : V ≤ C.cover i) (hj : V ≤ D.cover j) : Γ(X, V)ˣ :=
  unitOfSelfLinearEquiv (polarizationLocalEquiv C D d μ i j V hi hj)

@[simp] theorem polarizationUnit_val (i j : ι) (V : X.Opens)
    (hi : V ≤ C.cover i) (hj : V ≤ D.cover j) :
    (polarizationUnit C D d μ i j V hi hj : Γ(X, V)) =
      toLocal D d j V hj
        (polarizationSectionEquiv C D d μ V (fromLocal C 1 i V hi 1)) := rfl

theorem fromLocal_restrict (n : ℕ) (i : ι) {V W : X.Opens}
    (h : V ≤ W) (hi : W ≤ C.cover i) (a : Γ(X, W)) :
    restrictSections C n h (fromLocal C n i W hi a) =
      fromLocal C n i V (h.trans hi) (res h a) := by
  apply (localLinearEquiv C n i V (h.trans hi)).injective
  change toLocal C n i V (h.trans hi) _ = toLocal C n i V (h.trans hi) _
  rw [toLocal_restrict C n i h hi, toLocal_fromLocal, toLocal_fromLocal]

theorem polarizationUnit_naturality (i j : ι) {V W : X.Opens}
    (h : V ≤ W) (hi : W ≤ C.cover i) (hj : W ≤ D.cover j) :
    Units.map (res h).toMonoidHom (polarizationUnit C D d μ i j W hi hj) =
      polarizationUnit C D d μ i j V (h.trans hi) (h.trans hj) := by
  apply Units.ext
  change res h (toLocal D d j W hj
    (polarizationSectionEquiv C D d μ W (fromLocal C 1 i W hi 1))) =
      toLocal D d j V (h.trans hj)
        (polarizationSectionEquiv C D d μ V (fromLocal C 1 i V (h.trans hi) 1))
  rw [← toLocal_restrict, ← polarizationSectionEquiv_restrict, fromLocal_restrict, map_one]

theorem polarizationUnit_action (i j : ι) (V : X.Opens)
    (hi : V ≤ C.cover i) (hj : V ≤ D.cover j) (a : TwistedSections C 1 V) :
    toLocal D d j V hj (polarizationSectionEquiv C D d μ V a) =
      (polarizationUnit C D d μ i j V hi hj : Γ(X, V)) * toLocal C 1 i V hi a := by
  have h := selfLinearEquiv_apply (polarizationLocalEquiv C D d μ i j V hi hj)
    (toLocal C 1 i V hi a)
  change toLocal D d j V hj
    (polarizationSectionEquiv C D d μ V
      (fromLocal C 1 i V hi (toLocal C 1 i V hi a))) = _ at h
  rw [fromLocal_toLocal] at h
  exact h

/-- Changing any original local coefficient retains the full cocycle relation. -/
theorem toLocal_change (n : ℕ) (i j : ι) (V : X.Opens)
    (hi : V ≤ C.cover i) (hj : V ≤ C.cover j) (a : TwistedSections C n V) :
    toLocal C n i V hi a = (C.g i j V hi hj : Γ(X, V)) ^ n * toLocal C n j V hj a :=
  compatible_on C a i j V le_rfl hi hj

/-- One actual isomorphism forces the gauge identity on every overlap of both covers. -/
theorem polarizationUnit_overlap (i j k l : ι) (V : X.Opens)
    (hi : V ≤ C.cover i) (hj : V ≤ D.cover j)
    (hk : V ≤ C.cover k) (hl : V ≤ D.cover l) :
    (polarizationUnit C D d μ i j V hi hj : Γ(X, V)) * (C.g i k V hi hk : Γ(X, V)) =
      (D.g j l V hj hl : Γ(X, V)) ^ d *
        (polarizationUnit C D d μ k l V hk hl : Γ(X, V)) := by
  let a := fromLocal C 1 k V hk (1 : Γ(X, V))
  have h := toLocal_change D d j l V hj hl (polarizationSectionEquiv C D d μ V a)
  rw [polarizationUnit_action C D d μ i j V hi hj,
    polarizationUnit_action C D d μ k l V hk hl] at h
  rw [toLocal_change C 1 i k V hi hk a] at h
  simpa only [a, toLocal_fromLocal, pow_one, mul_one] using h

end ArithDyn.Extension.ProjTwist

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{max u v}} {ι : Type v} (C D : UnitCocycle X ι) (d : ℕ)
variable (μ : twistedModule C 1 ≅ twistedModule D d)

/-- Read an original global matching section on any smaller chart open. -/
def chartCoefficient {n : ℕ} {V : X.Opens} (a : TwistedSections C n V)
    (i : ι) (W : X.Opens) (hW : W ≤ V) (hi : W ≤ C.cover i) : Γ(X, W) :=
  toLocal C n i W hi (restrictSections C n hW a)

theorem chartCoefficient_restrict {n : ℕ} {V W Z : X.Opens}
    (a : TwistedSections C n V) (i : ι) (hZW : Z ≤ W) (hWV : W ≤ V)
    (hi : W ≤ C.cover i) :
    res hZW (chartCoefficient C a i W hWV hi) =
      chartCoefficient C a i Z (hZW.trans hWV) (hZW.trans hi) := by
  rw [chartCoefficient, ← toLocal_restrict, restrictSections_comp]
  rfl

theorem chartCoefficient_change {n : ℕ} {V : X.Opens}
    (a : TwistedSections C n V) (i j : ι) (W : X.Opens)
    (hW : W ≤ V) (hi : W ≤ C.cover i) (hj : W ≤ C.cover j) :
    chartCoefficient C a i W hW hi = (C.g i j W hi hj : Γ(X, W)) ^ n *
      chartCoefficient C a j W hW hj :=
  toLocal_change C n i j W hi hj _

variable (hCD : ∀ i, D.cover i ≤ C.cover i)

/-- One local coefficient in degree `n`, using the `n`th power of the same
unit extracted from the single original polarization. -/
def polarizationPowerCoefficient {n : ℕ} {V : X.Opens}
    (a : TwistedSections C n V) (i : ι) (W : X.Opens)
    (hW : W ≤ V) (hi : W ≤ D.cover i) : Γ(X, W) :=
  (polarizationUnit C D d μ i i W (hi.trans (hCD i)) hi : Γ(X, W)) ^ n *
    chartCoefficient C a i W hW (hi.trans (hCD i))

theorem polarizationPowerCoefficient_restrict {n : ℕ} {V W Z : X.Opens}
    (a : TwistedSections C n V) (i : ι) (hZW : Z ≤ W) (hWV : W ≤ V)
    (hi : W ≤ D.cover i) :
    res hZW (polarizationPowerCoefficient C D d μ hCD a i W hWV hi) =
      polarizationPowerCoefficient C D d μ hCD a i Z (hZW.trans hWV) (hZW.trans hi) := by
  unfold polarizationPowerCoefficient
  rw [map_mul, map_pow, chartCoefficient_restrict]
  have hu := congrArg (fun z : Γ(X, Z)ˣ => (z : Γ(X, Z)))
    (polarizationUnit_naturality C D d μ i i hZW (hi.trans (hCD i)) hi)
  rw [show res hZW (polarizationUnit C D d μ i i W (hi.trans (hCD i)) hi : Γ(X, W)) =
    (polarizationUnit C D d μ i i Z _ _ : Γ(X, Z)) from hu]

theorem polarizationPowerCoefficient_change {n : ℕ} {V : X.Opens}
    (a : TwistedSections C n V) (i j : ι) (W : X.Opens)
    (hW : W ≤ V) (hi : W ≤ D.cover i) (hj : W ≤ D.cover j) :
    polarizationPowerCoefficient C D d μ hCD a i W hW hi =
      (D.g i j W hi hj : Γ(X, W)) ^ (d * n) *
        polarizationPowerCoefficient C D d μ hCD a j W hW hj := by
  unfold polarizationPowerCoefficient
  rw [chartCoefficient_change C a i j W hW (hi.trans (hCD i)) (hj.trans (hCD j))]
  have hu := congrArg (fun z : Γ(X, W) => z ^ n)
    (polarizationUnit_overlap C D d μ i i j j W
      (hi.trans (hCD i)) hi (hj.trans (hCD j)) hj)
  dsimp only at hu
  rw [mul_pow, mul_pow, ← pow_mul] at hu
  rw [← mul_assoc, hu, mul_assoc]

/-- All degrees are constructed simultaneously from the one original isomorphism.
The target cover refines the source cover; equality of covers is a special case. -/
def polarizationPowerSections (n : ℕ) (V : X.Opens) (a : TwistedSections C n V) :
    TwistedSections D (d * n) V := by
  refine ⟨fun i => polarizationPowerCoefficient C D d μ hCD a i
    (V ⊓ D.cover i) inf_le_left inf_le_right, ?_⟩
  intro i j
  rw [polarizationPowerCoefficient_restrict, polarizationPowerCoefficient_restrict]
  exact polarizationPowerCoefficient_change C D d μ hCD a i j
    (overlap D V i j) (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right

@[simp] theorem polarizationPowerSections_apply (n : ℕ) (V : X.Opens)
    (a : TwistedSections C n V) (i : ι) :
    (polarizationPowerSections C D d μ hCD n V a).1 i =
      polarizationPowerCoefficient C D d μ hCD a i (V ⊓ D.cover i)
        inf_le_left inf_le_right := rfl

end ArithDyn.Extension.ProjTwist

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{max u v}} {ι : Type v} (C D : UnitCocycle X ι) (d : ℕ)
variable (μ : twistedModule C 1 ≅ twistedModule D d) (hCD : ∀ i, D.cover i ≤ C.cover i)

theorem polarizationPowerSections_add (n : ℕ) (V : X.Opens)
    (a b : TwistedSections C n V) :
    polarizationPowerSections C D d μ hCD n V (a + b) =
      polarizationPowerSections C D d μ hCD n V a +
        polarizationPowerSections C D d μ hCD n V b := by
  ext i
  simp only [polarizationPowerSections_apply, polarizationPowerCoefficient,
    chartCoefficient, toLocal, restrictSections_apply, Submodule.coe_add,
    Pi.add_apply, map_add, mul_add]

theorem polarizationPowerSections_smul (n : ℕ) (V : X.Opens)
    (r : Γ(X, V)) (a : TwistedSections C n V) :
    polarizationPowerSections C D d μ hCD n V (r • a) =
      r • polarizationPowerSections C D d μ hCD n V a := by
  ext i
  change _ * res _ (res _ (res inf_le_left r * a.1 i)) =
    res inf_le_left r * (_ * res _ (res _ (a.1 i)))
  simp only [map_mul, res_comp]
  ring

/-- Degree `n` is linear and derived from the same original polarization. -/
def polarizationPowerLinearMap (n : ℕ) (V : X.Opens) :
    TwistedSections C n V →ₗ[Γ(X, V)] TwistedSections D (d * n) V where
  toFun := polarizationPowerSections C D d μ hCD n V
  map_add' := polarizationPowerSections_add C D d μ hCD n V
  map_smul' := polarizationPowerSections_smul C D d μ hCD n V

/-- The maps of every degree retain the original restriction maps. -/
theorem polarizationPowerSections_restrict (n : ℕ) {V W : X.Opens}
    (h : V ≤ W) (a : TwistedSections C n W) :
    polarizationPowerSections C D d μ hCD n V (restrictSections C n h a) =
      restrictSections D (d * n) h (polarizationPowerSections C D d μ hCD n W a) := by
  ext i
  rw [restrictSections_apply, polarizationPowerSections_apply,
    polarizationPowerSections_apply, polarizationPowerCoefficient_restrict]
  unfold polarizationPowerCoefficient chartCoefficient
  rw [restrictSections_comp]

/-- The same unit powers preserve the multiplication between all degrees. -/
theorem polarizationPowerSections_mul_apply {n m : ℕ} {V : X.Opens}
    (a : TwistedSections C n V) (b : TwistedSections C m V) (i : ι) :
    (polarizationPowerSections C D d μ hCD (n + m) V (mulSections C a b)).1 i =
      (polarizationPowerSections C D d μ hCD n V a).1 i *
        (polarizationPowerSections C D d μ hCD m V b).1 i := by
  simp only [polarizationPowerSections_apply, polarizationPowerCoefficient,
    chartCoefficient, toLocal, restrictSections_apply, mulSections_apply, map_mul, pow_add]
  ring

/-- Degree zero preserves the actual multiplicative unit. -/
theorem polarizationPowerSections_zero_one_apply (V : X.Opens) (i : ι) :
    (polarizationPowerSections C D d μ hCD 0 V
      ⟨1, compatible_one C V⟩).1 i = 1 := by
  simp only [polarizationPowerSections_apply, polarizationPowerCoefficient,
    chartCoefficient, toLocal, restrictSections_apply, pow_zero, one_mul]
  change res _ (res _ 1) = 1
  rw [map_one, map_one]

/-- Degree one is exactly the action of the given original isomorphism. -/
theorem polarizationPowerSections_one_apply (V : X.Opens)
    (a : TwistedSections C 1 V) (i : ι) :
    (polarizationPowerSections C D d μ hCD 1 V a).1 i =
      (polarizationSectionEquiv C D d μ V a).1 i := by
  rw [polarizationPowerSections_apply]
  unfold polarizationPowerCoefficient chartCoefficient
  rw [pow_one, ← polarizationUnit_action,
    polarizationSectionEquiv_restrict]
  change res _ (res _ ((polarizationSectionEquiv C D d μ V a).1 i)) = _
  rw [res_comp, res_refl]

end ArithDyn.Extension.ProjTwist
