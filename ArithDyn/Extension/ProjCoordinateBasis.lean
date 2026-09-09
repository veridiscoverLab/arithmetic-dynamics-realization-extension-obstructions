import ArithDyn.Extension.ProjCoordinateCocycle

/-!
# A homogeneous polynomial as a local basis of the standard twist

On `D₊(F)`, a degree-`d` polynomial gives the basis whose coefficient on the
`i`-th coordinate chart is `F / Xᵢ^d`.  The inverse coefficients are `Xᵢ^d / F`.
These are units in the original structure sheaf and obey all overlap equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

open CategoryTheory TopologicalSpace AlgebraicGeometry HomogeneousLocalization MvPolynomial

namespace ArithDyn.Extension.ProjTwist

section Fractions

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A denominator invertible on an open has every power invertible there. -/
theorem basicOpen_le_pow (a : A) (m : ℕ) :
    Proj.basicOpen 𝒜 a ≤ Proj.basicOpen 𝒜 (a ^ m) := by
  intro p hp
  exact p.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hp m

/-- Powers of ratios are proved inside the actual homogeneous localizations. -/
theorem homogeneousRatio_pow {n : ℕ} (a b : A) (ha : a ∈ 𝒜 n) (hb : b ∈ 𝒜 n)
    (m : ℕ) (V : (Proj 𝒜).Opens) (hV : V ≤ Proj.basicOpen 𝒜 b) :
    homogeneousRatio 𝒜 a b ha hb V hV ^ m =
      homogeneousRatio 𝒜 (a ^ m) (b ^ m) (SetLike.pow_mem_graded m ha)
        (SetLike.pow_mem_graded m hb) V (hV.trans (basicOpen_le_pow 𝒜 b m)) := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change ((homogeneousRatio 𝒜 a b ha hb V hV).1 x ^ m).val = _
  rw [HomogeneousLocalization.val_pow]
  change (Localization.mk a ⟨b, hV x.2⟩ :
      Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) ^ m =
    Localization.mk (a ^ m) ⟨b ^ m, _⟩
  simpa only [Localization.mk_eq_mk'] using
    (IsLocalization.mk'_pow (S := Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl)
      a ⟨b, hV x.2⟩ m).symm

end Fractions

section UnitFrames

variable {Y : Scheme.{u}} {κ : Type v} (C : UnitCocycle Y κ)

private theorem normalized_units_eq {R : Type w} [CommRing R]
    (a b : Rˣ) (g x y : R) (hab : (a : R) = g * b) (hxy : x = g * y) :
    (↑a⁻¹ : R) * x = (↑b⁻¹ : R) * y := by
  apply a.isUnit.mul_right_injective
  calc
    (a : R) * ((↑a⁻¹ : R) * x) = x := by simp [← mul_assoc]
    _ = g * y := hxy
    _ = (a : R) * ((↑b⁻¹ : R) * y) := by
      rw [hab]
      calc
        g * y = g * ((b : R) * ↑b⁻¹ * y) := by simp
        _ = g * (b : R) * ((↑b⁻¹ : R) * y) := by ac_rfl

/-- A compatible family of units multiplies scalars into actual twisted sections. -/
def unitFrameScalarMap (n : ℕ) (V : Y.Opens)
    (b : (i : κ) → Γ(Y, V ⊓ C.cover i)ˣ)
    (hb : Compatible C n V (fun i => (b i : Γ(Y, V ⊓ C.cover i)))) :
    Γ(Y, V) →ₗ[Γ(Y, V)] TwistedSections C n V where
  toFun r := r • (⟨fun i => b i, hb⟩ : TwistedSections C n V)
  map_add' r s := add_smul r s _
  map_smul' r s := mul_smul r s _

/-- The inverse local coefficients agree on every common open. -/
theorem unitFrame_normalized_compatible (n : ℕ) (V : Y.Opens)
    (b : (i : κ) → Γ(Y, V ⊓ C.cover i)ˣ)
    (hb : Compatible C n V (fun i => (b i : Γ(Y, V ⊓ C.cover i))))
    (a : TwistedSections C n V) (i j : κ) (W : Y.Opens)
    (hV : W ≤ V) (hi : W ≤ C.cover i) (hj : W ≤ C.cover j) :
    res (le_inf hV hi) ((↑(b i)⁻¹ : Γ(Y, V ⊓ C.cover i)) * a.1 i) =
      res (le_inf hV hj) ((↑(b j)⁻¹ : Γ(Y, V ⊓ C.cover j)) * a.1 j) := by
  rw [map_mul, map_mul]
  exact normalized_units_eq
    (Units.map (res (le_inf hV hi)).toMonoidHom (b i))
    (Units.map (res (le_inf hV hj)).toMonoidHom (b j))
    ((C.g i j W hi hj : Γ(Y, W)) ^ n)
    (res (le_inf hV hi) (a.1 i)) (res (le_inf hV hj) (a.1 j))
    (compatible_on C (⟨fun l => b l, hb⟩ : TwistedSections C n V) i j W hV hi hj)
    (compatible_on C a i j W hV hi hj)

/-- The actual sheaf axiom glues the normalized coefficients; all chart equations
are retained in the inverse, including on a nonreduced scheme. -/
theorem unitFrameScalarMap_bijective (n : ℕ) (V : Y.Opens)
    (b : (i : κ) → Γ(Y, V ⊓ C.cover i)ˣ)
    (hb : Compatible C n V (fun i => (b i : Γ(Y, V ⊓ C.cover i)))) :
    Function.Bijective (unitFrameScalarMap C n V b hb) := by
  have hcover : V ≤ ⨆ i, V ⊓ C.cover i := by
    rw [← inf_iSup_eq, C.covers, inf_top_eq]
  constructor
  · intro r s hrs
    apply Y.sheaf.eq_of_locally_eq' (fun i => V ⊓ C.cover i) V
      (fun _ => homOfLE inf_le_left) hcover
    intro i
    exact (b i).isUnit.mul_left_injective
      (congrArg (fun t : TwistedSections C n V => t.1 i) hrs)
  · intro a
    obtain ⟨r, hr, _⟩ := Y.sheaf.existsUnique_gluing' (fun i => V ⊓ C.cover i) V
      (fun _ => homOfLE inf_le_left) hcover
      (fun i => (↑(b i)⁻¹ : Γ(Y, V ⊓ C.cover i)) * a.1 i) (by
        intro i j
        exact unitFrame_normalized_compatible C n V b hb a i j
          ((V ⊓ C.cover i) ⊓ (V ⊓ C.cover j))
          (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
          (inf_le_right.trans inf_le_right))
    refine ⟨r, ?_⟩
    ext i
    change res inf_le_left r * (b i : Γ(Y, V ⊓ C.cover i)) = a.1 i
    have hi : res inf_le_left r = (↑(b i)⁻¹ : Γ(Y, V ⊓ C.cover i)) * a.1 i := hr i
    rw [hi]
    calc
      (↑(b i)⁻¹ * a.1 i) * ↑(b i) = (↑(b i)⁻¹ * ↑(b i)) * a.1 i := by ac_rfl
      _ = a.1 i := by simp

/-- A unit frame supplies an actual linear equivalence, not a dimension count. -/
def unitFrameLinearEquiv (n : ℕ) (V : Y.Opens)
    (b : (i : κ) → Γ(Y, V ⊓ C.cover i)ˣ)
    (hb : Compatible C n V (fun i => (b i : Γ(Y, V ⊓ C.cover i)))) :
    Γ(Y, V) ≃ₗ[Γ(Y, V)] TwistedSections C n V :=
  LinearEquiv.ofBijective (unitFrameScalarMap C n V b hb)
    (unitFrameScalarMap_bijective C n V b hb)

/-- Every coefficient of the glued inverse is division by the original frame. -/
theorem unitFrameLinearEquiv_symm_apply_res (n : ℕ) (V : Y.Opens)
    (b : (i : κ) → Γ(Y, V ⊓ C.cover i)ˣ)
    (hb : Compatible C n V (fun i => (b i : Γ(Y, V ⊓ C.cover i))))
    (a : TwistedSections C n V) (i : κ) :
    res inf_le_left ((unitFrameLinearEquiv C n V b hb).symm a) =
      (↑(b i)⁻¹ : Γ(Y, V ⊓ C.cover i)) * a.1 i := by
  have he := congrArg (fun t : TwistedSections C n V => t.1 i)
    ((unitFrameLinearEquiv C n V b hb).apply_symm_apply a)
  change res inf_le_left ((unitFrameLinearEquiv C n V b hb).symm a) *
    (b i : Γ(Y, V ⊓ C.cover i)) = a.1 i at he
  calc
    res inf_le_left ((unitFrameLinearEquiv C n V b hb).symm a) =
        (res inf_le_left ((unitFrameLinearEquiv C n V b hb).symm a) * ↑(b i)) *
          (↑(b i)⁻¹ : Γ(Y, V ⊓ C.cover i)) := by simp [mul_assoc]
    _ = a.1 i * (↑(b i)⁻¹ : Γ(Y, V ⊓ C.cover i)) := by rw [he]
    _ = _ := mul_comm _ _

end UnitFrames

section Coordinates

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra
variable {k : Type u} {ι : Type v} [Field k]

theorem coordinate_pow_homogeneous (i : ι) (d : ℕ) :
    (X i : MvPolynomial ι k) ^ d ∈ homogeneousSubmodule ι k d := by
  simpa only [smul_eq_mul, mul_one] using
    SetLike.pow_mem_graded (A := homogeneousSubmodule ι k) d (isHomogeneous_X k i)

/-- `F / Xᵢ^d` is a unit wherever both `F` and `Xᵢ` are invertible. -/
def homogeneousBasisUnit (d : ℕ) (F : MvPolynomial ι k) (hF : F.IsHomogeneous d)
    (V : (Proj (homogeneousSubmodule ι k)).Opens)
    (hV : V ≤ Proj.basicOpen (homogeneousSubmodule ι k) F) (i : ι) :
    Γ(Proj (homogeneousSubmodule ι k), V ⊓ (standardCocycle k ι).cover i)ˣ :=
  homogeneousRatioUnit (homogeneousSubmodule ι k) (X i ^ d) F
    (coordinate_pow_homogeneous i d) hF _
    (inf_le_right.trans (basicOpen_le_pow (homogeneousSubmodule ι k) (X i) d))
    (inf_le_left.trans hV)

/-- The complete coefficient family of `F` obeys every standard twist overlap. -/
theorem homogeneousBasis_compatible (d : ℕ) (F : MvPolynomial ι k)
    (hF : F.IsHomogeneous d) (V : (Proj (homogeneousSubmodule ι k)).Opens)
    (hV : V ≤ Proj.basicOpen (homogeneousSubmodule ι k) F) :
    Compatible (standardCocycle k ι) d V
      (fun i => (homogeneousBasisUnit d F hF V hV i :
        Γ(Proj (homogeneousSubmodule ι k), V ⊓ (standardCocycle k ι).cover i))) := by
  intro i j
  dsimp only [homogeneousBasisUnit, homogeneousRatioUnit]
  rw [res_homogeneousRatio, res_homogeneousRatio, standardCocycle_g_val,
    homogeneousRatio_pow]
  simp only [smul_eq_mul, mul_one]
  exact (homogeneousRatio_comp (homogeneousSubmodule ι k) (X i ^ d) (X j ^ d) F
    (coordinate_pow_homogeneous i d) (coordinate_pow_homogeneous j d) hF
    (overlap (standardCocycle k ι) V i j)
    ((inf_le_left.trans inf_le_right).trans
      (basicOpen_le_pow (homogeneousSubmodule ι k) (X i) d))
    (inf_le_right.trans (basicOpen_le_pow (homogeneousSubmodule ι k) (X j) d))).symm

/-- The actual compatible section defined by the original polynomial. -/
def homogeneousBasisSection (d : ℕ) (F : MvPolynomial ι k) (hF : F.IsHomogeneous d)
    (V : (Proj (homogeneousSubmodule ι k)).Opens)
    (hV : V ≤ Proj.basicOpen (homogeneousSubmodule ι k) F) :
    TwistedSections (standardCocycle k ι) d V :=
  ⟨fun i => homogeneousBasisUnit d F hF V hV i,
    homogeneousBasis_compatible d F hF V hV⟩

/-- Dividing by the original `F` gives coordinates in the basis on `D₊(F)`. -/
def homogeneousBasisLinearEquiv (d : ℕ) (F : MvPolynomial ι k) (hF : F.IsHomogeneous d)
    (V : (Proj (homogeneousSubmodule ι k)).Opens)
    (hV : V ≤ Proj.basicOpen (homogeneousSubmodule ι k) F) :
    TwistedSections (standardCocycle k ι) d V ≃ₗ[Γ(Proj (homogeneousSubmodule ι k), V)]
      Γ(Proj (homogeneousSubmodule ι k), V) :=
  (unitFrameLinearEquiv (standardCocycle k ι) d V
    (homogeneousBasisUnit d F hF V hV) (homogeneousBasis_compatible d F hF V hV)).symm

@[simp] theorem homogeneousBasisLinearEquiv_symm_apply
    (d : ℕ) (F : MvPolynomial ι k) (hF : F.IsHomogeneous d)
    (V : (Proj (homogeneousSubmodule ι k)).Opens)
    (hV : V ≤ Proj.basicOpen (homogeneousSubmodule ι k) F)
    (r : Γ(Proj (homogeneousSubmodule ι k), V)) :
    (homogeneousBasisLinearEquiv d F hF V hV).symm r =
      r • homogeneousBasisSection d F hF V hV := rfl

/-- The inverse coefficient is `Xᵢ^d / F`, on every coordinate chart. -/
theorem homogeneousBasisLinearEquiv_apply_res
    (d : ℕ) (F : MvPolynomial ι k) (hF : F.IsHomogeneous d)
    (V : (Proj (homogeneousSubmodule ι k)).Opens)
    (hV : V ≤ Proj.basicOpen (homogeneousSubmodule ι k) F)
    (a : TwistedSections (standardCocycle k ι) d V) (i : ι) :
    res inf_le_left (homogeneousBasisLinearEquiv d F hF V hV a) =
      homogeneousRatio (homogeneousSubmodule ι k) (X i ^ d) F
        (coordinate_pow_homogeneous i d) hF _ (inf_le_left.trans hV) * a.1 i :=
  unitFrameLinearEquiv_symm_apply_res (standardCocycle k ι) d V
    (homogeneousBasisUnit d F hF V hV) (homogeneousBasis_compatible d F hF V hV) a i

@[simp] theorem homogeneousBasisLinearEquiv_basis
    (d : ℕ) (F : MvPolynomial ι k) (hF : F.IsHomogeneous d)
    (V : (Proj (homogeneousSubmodule ι k)).Opens)
    (hV : V ≤ Proj.basicOpen (homogeneousSubmodule ι k) F) :
    homogeneousBasisLinearEquiv d F hF V hV (homogeneousBasisSection d F hF V hV) = 1 := by
  simpa only [homogeneousBasisLinearEquiv_symm_apply, one_smul] using
    (homogeneousBasisLinearEquiv d F hF V hV).apply_symm_apply 1

/-- Multiplication by the same polynomial commutes with every restriction. -/
theorem homogeneousBasis_expand_restrict
    (d : ℕ) (F : MvPolynomial ι k) (hF : F.IsHomogeneous d)
    {V W : (Proj (homogeneousSubmodule ι k)).Opens} (h : V ≤ W)
    (hW : W ≤ Proj.basicOpen (homogeneousSubmodule ι k) F)
    (r : Γ(Proj (homogeneousSubmodule ι k), W)) :
    restrictSections (standardCocycle k ι) d h
        ((homogeneousBasisLinearEquiv d F hF W hW).symm r) =
      (homogeneousBasisLinearEquiv d F hF V (h.trans hW)).symm (res h r) := by
  ext i
  change res (inf_le_inf h le_rfl)
      (res inf_le_left r * (homogeneousBasisUnit d F hF W hW i :
        Γ(Proj (homogeneousSubmodule ι k), W ⊓ (standardCocycle k ι).cover i))) =
    res inf_le_left (res h r) * (homogeneousBasisUnit d F hF V (h.trans hW) i :
      Γ(Proj (homogeneousSubmodule ι k), V ⊓ (standardCocycle k ι).cover i))
  dsimp only [homogeneousBasisUnit, homogeneousRatioUnit]
  rw [map_mul, res_comp, res_homogeneousRatio, res_comp]

/-- Division in the basis `F` is natural on all subopens of `D₊(F)`. -/
theorem homogeneousBasisLinearEquiv_restrict
    (d : ℕ) (F : MvPolynomial ι k) (hF : F.IsHomogeneous d)
    {V W : (Proj (homogeneousSubmodule ι k)).Opens} (h : V ≤ W)
    (hW : W ≤ Proj.basicOpen (homogeneousSubmodule ι k) F)
    (a : TwistedSections (standardCocycle k ι) d W) :
    homogeneousBasisLinearEquiv d F hF V (h.trans hW)
        (restrictSections (standardCocycle k ι) d h a) =
      res h (homogeneousBasisLinearEquiv d F hF W hW a) := by
  apply (homogeneousBasisLinearEquiv d F hF V (h.trans hW)).symm.injective
  rw [LinearEquiv.symm_apply_apply, ← homogeneousBasis_expand_restrict d F hF h hW,
    LinearEquiv.symm_apply_apply]

/-- The actual restriction of standard `O(d)` to `D₊(F)` has basis `F`. -/
def homogeneousBasisRestrictionIso
    (d : ℕ) (F : MvPolynomial ι k) (hF : F.IsHomogeneous d)
    (U : (Proj (homogeneousSubmodule ι k)).Opens)
    (hU : U ≤ Proj.basicOpen (homogeneousSubmodule ι k) F) :
    Scheme.Modules.restrict (standardO k ι d) U.ι ≅ unitStructureModule U.toScheme := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V => ?_) ?_
  · exact (ModuleCat.restrictScalarsId'App
      (((forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv).hom)
      (by simp only [Scheme.Opens.ι_appIso]; rfl) _) ≪≫
      (homogeneousBasisLinearEquiv d F hF (U.ι ''ᵁ V.unop)
        ((U.ι_image_le V.unop).trans hU)).toModuleIso
  · intro V W f
    ext a
    exact homogeneousBasisLinearEquiv_restrict d F hF (U.ι.image_mono f.unop.le)
      ((U.ι_image_le V.unop).trans hU) a

/-- The same basis for the categorical module pullback along the open immersion. -/
def homogeneousBasisPullbackIso
    (d : ℕ) (F : MvPolynomial ι k) (hF : F.IsHomogeneous d)
    (U : (Proj (homogeneousSubmodule ι k)).Opens)
    (hU : U ≤ Proj.basicOpen (homogeneousSubmodule ι k) F) :
    (Scheme.Modules.pullback U.ι).obj (standardO k ι d) ≅ unitStructureModule U.toScheme :=
  ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (standardO k ι d)).symm ≪≫
    homogeneousBasisRestrictionIso d F hF U hU

end Coordinates

end ArithDyn.Extension.ProjTwist
