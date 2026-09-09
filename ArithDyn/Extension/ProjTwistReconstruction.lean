import ArithDyn.Extension.ProjTwistFrames

/-!
# Reconstruction of an original module from actual local frames

The transition functions are derived from the original module and its actual
restriction isomorphisms.  No cocycle or global reconstruction isomorphism is input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace ArithDyn.Extension.ProjTwist

section Linear
variable {R : Type*} [CommRing R]

theorem selfLinearEquiv_apply (e : R ≃ₗ[R] R) (r : R) : e r = e 1 * r := by
  simpa only [smul_eq_mul, mul_one, mul_comm] using e.map_smul r (1 : R)

/-- The multiplier of a rank-one linear automorphism is an actual ring unit. -/
def unitOfSelfLinearEquiv (e : R ≃ₗ[R] R) : Rˣ where
  val := e 1
  inv := e.symm 1
  val_inv := by
    have h := e.apply_symm_apply (1 : R)
    rw [selfLinearEquiv_apply e (e.symm 1)] at h
    exact h
  inv_val := by
    have h := e.symm_apply_apply (1 : R)
    rw [selfLinearEquiv_apply e.symm (e 1)] at h
    exact h

@[simp] theorem unitOfSelfLinearEquiv_val (e : R ≃ₗ[R] R) :
    (unitOfSelfLinearEquiv e : R) = e 1 := rfl

end Linear

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type v}
variable (U : ι → X.Opens) (hcover : iSup U = ⊤)
variable (e : ∀ i, M.restrict (U i).ι ≅ SheafOfModules.unit (U i).toScheme.ringCatSheaf)

/-- The change from chart `j` to chart `i`, extracted from the original sheaf. -/
def frameChange (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    Γ(X, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  (localFrameCoordinates M (e j) V hj).symm.trans
    (localFrameCoordinates M (e i) V hi)

@[simp] theorem frameChange_apply (i j : ι) (V : X.Opens)
    (hi : V ≤ U i) (hj : V ≤ U j) (r : Γ(X, V)) :
    frameChange M U e i j V hi hj r =
      localFrameCoordinates M (e i) V hi ((localFrameCoordinates M (e j) V hj).symm r) := rfl

/-- The complete transition cocycle reconstructed from actual restriction bases. -/
def framesCocycle : UnitCocycle X ι where
  cover := U
  covers := hcover
  g i j V hi hj := unitOfSelfLinearEquiv (frameChange M U e i j V hi hj)
  naturality i j V W h hi hj := by
    apply Units.ext
    change res h (localFrameCoordinates M (e i) W hi
      ((localFrameCoordinates M (e j) W hj).symm 1)) =
        localFrameCoordinates M (e i) V (h.trans hi)
          ((localFrameCoordinates M (e j) V (h.trans hj)).symm 1)
    rw [← localFrameCoordinates_restrict,
      localFrameCoordinates_symm_restrict, map_one]
  self i V hi := by
    apply Units.ext
    exact (localFrameCoordinates M (e i) V hi).apply_symm_apply 1
  comp i j k V hi hj hk := by
    apply Units.ext
    change frameChange M U e i j V hi hj 1 * frameChange M U e j k V hj hk 1 =
      frameChange M U e i k V hi hk 1
    rw [← selfLinearEquiv_apply]
    simp only [frameChange_apply, LinearEquiv.symm_apply_apply]

@[simp] theorem framesCocycle_cover (i : ι) : (framesCocycle M U hcover e).cover i = U i := rfl

@[simp] theorem framesCocycle_g_val (i j : ι) (V : X.Opens)
    (hi : V ≤ U i) (hj : V ≤ U j) :
    ((framesCocycle M U hcover e).g i j V hi hj : Γ(X, V)) =
      localFrameCoordinates M (e i) V hi ((localFrameCoordinates M (e j) V hj).symm 1) := rfl

/-- Every original section obeys exactly the reconstructed overlap equations. -/
theorem frame_coordinates_change (i j : ι) (V : X.Opens)
    (hi : V ≤ U i) (hj : V ≤ U j) (s : Γ(M, V)) :
    localFrameCoordinates M (e i) V hi s =
      ((framesCocycle M U hcover e).g i j V hi hj : Γ(X, V)) *
        localFrameCoordinates M (e j) V hj s := by
  have h := selfLinearEquiv_apply (frameChange M U e i j V hi hj)
    (localFrameCoordinates M (e j) V hj s)
  simpa only [frameChange_apply, LinearEquiv.symm_apply_apply] using h

/-- Send an original section to all of its local coordinates simultaneously. -/
def reconstructionSections (V : X.Opens) (s : Γ(M, V)) :
    TwistedSections (framesCocycle M U hcover e) 1 V := by
  refine ⟨fun i => localFrameCoordinates M (e i) (V ⊓ U i) inf_le_right
    (moduleRes M inf_le_left s), ?_⟩
  intro i j
  change res _ (localFrameCoordinates M (e i) _ _ _) =
    _ ^ 1 * res _ (localFrameCoordinates M (e j) _ _ _)
  simp only [pow_one, framesCocycle_cover, overlap]
  rw [← localFrameCoordinates_restrict M (e i)
      (V := V ⊓ U i ⊓ U j) (W := V ⊓ U i) inf_le_left inf_le_right,
    ← localFrameCoordinates_restrict M (e j)
      (V := V ⊓ U i ⊓ U j) (W := V ⊓ U j)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) inf_le_right]
  simp only [moduleRes_comp M]
  exact frame_coordinates_change M U hcover e i j _ _ _ _

@[simp] theorem reconstructionSections_apply (V : X.Opens) (s : Γ(M, V)) (i : ι) :
    (reconstructionSections M U hcover e V s).1 i =
      localFrameCoordinates M (e i) (V ⊓ U i) inf_le_right
        (moduleRes M inf_le_left s) := rfl

/-- The full coordinate map is linear over the original ring of sections. -/
def reconstructionLinearMap (V : X.Opens) :
    Γ(M, V) →ₗ[Γ(X, V)] TwistedSections (framesCocycle M U hcover e) 1 V where
  toFun := reconstructionSections M U hcover e V
  map_add' s t := by ext i; simp only [reconstructionSections_apply, map_add]; rfl
  map_smul' r s := by
    ext i
    change localFrameCoordinates M (e i) _ _ (moduleRes M _ (r • s)) =
      res inf_le_left r * _
    rw [moduleRes_smul, map_smul]
    rfl

theorem reconstructionSections_restrict {V W : X.Opens} (h : V ≤ W) (s : Γ(M, W)) :
    reconstructionSections M U hcover e V (moduleRes M h s) =
      restrictSections (framesCocycle M U hcover e) 1 h
        (reconstructionSections M U hcover e W s) := by
  ext i
  change localFrameCoordinates M (e i) _ _ (moduleRes M _ (moduleRes M _ s)) =
    res _ (localFrameCoordinates M (e i) _ _ (moduleRes M _ s))
  rw [← localFrameCoordinates_restrict, moduleRes_comp, moduleRes_comp]

theorem reconstructionSections_bijective (V : X.Opens) :
    Function.Bijective (reconstructionSections M U hcover e V) := by
  let S : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  have hc : V ≤ ⨆ i, V ⊓ U i := by rw [← inf_iSup_eq, hcover, inf_top_eq]
  constructor
  · intro s t h
    apply S.eq_of_locally_eq' (fun i => V ⊓ U i) V
      (fun _ => homOfLE inf_le_left) hc
    intro i
    apply (localFrameCoordinates M (e i) (V ⊓ U i) inf_le_right).injective
    exact congrArg (fun a => a.1 i) h
  · intro a
    let s : ∀ i, Γ(M, V ⊓ U i) := fun i =>
      (localFrameCoordinates M (e i) (V ⊓ U i) inf_le_right).symm (a.1 i)
    have hs : TopCat.Presheaf.IsCompatible M.presheaf (fun i => V ⊓ U i) s := by
      intro i j
      let W := (V ⊓ U i) ⊓ (V ⊓ U j)
      have hi : W ≤ U i := inf_le_left.trans inf_le_right
      have hj : W ≤ U j := inf_le_right.trans inf_le_right
      apply (localFrameCoordinates M (e i) W hi).injective
      change localFrameCoordinates M (e i) W hi (moduleRes M inf_le_left (s i)) =
        localFrameCoordinates M (e i) W hi (moduleRes M inf_le_right (s j))
      rw [localFrameCoordinates_restrict M (e i) inf_le_left inf_le_right,
        frame_coordinates_change M U hcover e i j W hi hj,
        localFrameCoordinates_restrict M (e j) inf_le_right inf_le_right]
      simp only [s, LinearEquiv.apply_symm_apply]
      have ha := compatible_on (framesCocycle M U hcover e) a i j W
        (inf_le_left.trans inf_le_left) hi hj
      simpa only [pow_one] using ha
    obtain ⟨t, ht, _⟩ := S.existsUnique_gluing' (fun i => V ⊓ U i) V
      (fun _ => homOfLE inf_le_left) hc s hs
    refine ⟨t, ?_⟩
    ext i
    change localFrameCoordinates M (e i) (V ⊓ U i) inf_le_right
      (moduleRes M inf_le_left t) = a.1 i
    rw [show moduleRes M inf_le_left t = s i from ht i]
    exact LinearEquiv.apply_symm_apply _ _

/-- The original sections and the reconstructed matching families are linearly identical. -/
def reconstructionLinearEquiv (V : X.Opens) :
    Γ(M, V) ≃ₗ[Γ(X, V)] TwistedSections (framesCocycle M U hcover e) 1 V :=
  LinearEquiv.ofBijective (reconstructionLinearMap M U hcover e V)
    (reconstructionSections_bijective M U hcover e V)

end ArithDyn.Extension.ProjTwist

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{max u v}} (M : X.Modules) {ι : Type v}
variable (U : ι → X.Opens) (hcover : iSup U = ⊤)
variable (e : ∀ i, M.restrict (U i).ι ≅ SheafOfModules.unit (U i).toScheme.ringCatSheaf)

/-- Reconstruction of the original module as an actual module-sheaf isomorphism. -/
def reconstructFromFramesIso :
    M ≅ twistedModule (framesCocycle M U hcover e) 1 := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V => ?_) ?_
  · exact (reconstructionLinearEquiv M U hcover e V.unop).toModuleIso
  · intro V W h
    ext s
    exact reconstructionSections_restrict M U hcover e h.unop.le s

@[simp] theorem reconstructFromFramesIso_hom_app (V : X.Opens) (s : Γ(M, V)) :
    Modules.Hom.app (reconstructFromFramesIso M U hcover e).hom V s =
      reconstructionSections M U hcover e V s := rfl

/-- A prescribed cocycle is identified by its actual transition values. -/
theorem framesCocycle_eq (C : UnitCocycle X ι)
    (b : ∀ i, M.restrict (C.cover i).ι ≅ SheafOfModules.unit (C.cover i).toScheme.ringCatSheaf)
    (h : ∀ (i j : ι) (V : X.Opens) (hi : V ≤ C.cover i) (hj : V ≤ C.cover j),
      localFrameCoordinates M (b i) V hi ((localFrameCoordinates M (b j) V hj).symm 1) =
        (C.g i j V hi hj : Γ(X, V))) :
    framesCocycle M C.cover C.covers b = C := by
  cases C
  unfold framesCocycle
  congr 1
  funext i j V hi hj
  apply Units.ext
  exact h i j V hi hj

/-- Actual local bases with the specified transitions reconstruct the original module. -/
def reconstructWithCocycleIso (C : UnitCocycle X ι)
    (b : ∀ i, M.restrict (C.cover i).ι ≅ SheafOfModules.unit (C.cover i).toScheme.ringCatSheaf)
    (h : ∀ (i j : ι) (V : X.Opens) (hi : V ≤ C.cover i) (hj : V ≤ C.cover j),
      localFrameCoordinates M (b i) V hi ((localFrameCoordinates M (b j) V hj).symm 1) =
        (C.g i j V hi hj : Γ(X, V))) : M ≅ twistedModule C 1 :=
  reconstructFromFramesIso M C.cover C.covers b ≪≫
    eqToIso (congrArg (fun D => twistedModule D 1) (framesCocycle_eq M C b h))

end ArithDyn.Extension.ProjTwist
