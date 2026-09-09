import ArithDyn.Extension.ProjTwistLocal

/-!
# Coordinates derived from actual local trivializations

Every coordinate map is extracted from a morphism of the original module sheaf.
Restriction compatibility is proved from its naturality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{u}} (M : X.Modules)

/-- Restriction in the original module sheaf. -/
abbrev moduleRes {U V : X.Opens} (h : U ≤ V) : Γ(M, V) →+ Γ(M, U) :=
  (M.presheaf.map (homOfLE h).op).hom

@[simp] theorem moduleRes_refl (U : X.Opens) (s : Γ(M, U)) :
    moduleRes M le_rfl s = s := by
  change (M.presheaf.map (𝟙 (op U))) s = s
  rw [M.presheaf.map_id]
  rfl

@[simp] theorem moduleRes_comp {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W)
    (s : Γ(M, W)) :
    moduleRes M hUV (moduleRes M hVW s) = moduleRes M (hUV.trans hVW) s := by
  change ((M.presheaf.map (homOfLE hVW).op) ≫ M.presheaf.map (homOfLE hUV).op) s = _
  rw [← M.presheaf.map_comp]
  rfl

theorem moduleRes_smul {U V : X.Opens} (h : U ≤ V) (r : Γ(X, V)) (s : Γ(M, V)) :
    moduleRes M h (r • s) = res h r • moduleRes M h s :=
  Modules.map_smul M (homOfLE h) r s

/-- Evaluate a genuine local module isomorphism on a smaller chart open. -/
def frameCoordinatesOnImage {U : X.Opens}
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : U.toScheme.Opens) :
    Γ(M, U.ι ''ᵁ W) ≃ₗ[Γ(X, U.ι ''ᵁ W)] Γ(X, U.ι ''ᵁ W) :=
  ((ModuleCat.restrictScalarsId'App
    (((forget₂ CommRingCat RingCat).map (U.ι.appIso W).inv).hom)
    (by simp only [Scheme.Opens.ι_appIso]; rfl)
    (M.val.obj (op (U.ι ''ᵁ W)))).symm ≪≫
    (SheafOfModules.evaluation U.toScheme.ringCatSheaf (op W)).mapIso e).toLinearEquiv

@[simp] theorem frameCoordinatesOnImage_apply {U : X.Opens}
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : U.toScheme.Opens) (s : Γ(M, U.ι ''ᵁ W)) :
    frameCoordinatesOnImage M e W s = Modules.Hom.app e.hom W s := rfl

theorem frameCoordinatesOnImage_restrict {U : X.Opens}
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    {V W : U.toScheme.Opens} (h : V ≤ W) (s : Γ(M, U.ι ''ᵁ W)) :
    frameCoordinatesOnImage M e V (moduleRes M (U.ι.image_mono h) s) =
      res (U.ι.image_mono h) (frameCoordinatesOnImage M e W s) := by
  exact congrArg (fun z => z s) (e.hom.mapPresheaf.naturality (homOfLE h).op)

/-- Transport a coordinate frame along equality of the actual opens. -/
def transportFrame {U V : X.Opens} (h : U = V)
    (e : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U)) : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V) := h ▸ e

theorem transportFrame_apply {U V : X.Opens} (h : U = V)
    (e : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U)) (s : Γ(M, V)) :
    transportFrame M h e s = res h.symm.le (e (moduleRes M h.le s)) := by
  subst V
  simp only [transportFrame, moduleRes_refl, res_refl]

theorem image_preimage_eq_of_le {U V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr h]

/-- The frame on every original open contained in its trivializing chart. -/
def localFrameCoordinates {U : X.Opens}
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V : X.Opens) (hV : V ≤ U) : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  transportFrame M (image_preimage_eq_of_le hV)
    (frameCoordinatesOnImage M e (U.ι ⁻¹ᵁ V))

theorem localFrameCoordinates_apply {U : X.Opens}
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V : X.Opens) (hV : V ≤ U) (s : Γ(M, V)) :
    localFrameCoordinates M e V hV s =
      res (image_preimage_eq_of_le hV).symm.le
        (frameCoordinatesOnImage M e (U.ι ⁻¹ᵁ V)
          (moduleRes M (image_preimage_eq_of_le hV).le s)) :=
  transportFrame_apply M _ _ _

/-- Compatibility with restriction follows from the actual sheaf morphism. -/
theorem localFrameCoordinates_restrict {U V W : X.Opens}
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ W) (hW : W ≤ U) (s : Γ(M, W)) :
    localFrameCoordinates M e V (h.trans hW) (moduleRes M h s) =
      res h (localFrameCoordinates M e W hW s) := by
  rw [localFrameCoordinates_apply, localFrameCoordinates_apply, res_comp, moduleRes_comp]
  have he := frameCoordinatesOnImage_restrict M e (U.ι.preimage_mono h)
    (moduleRes M (image_preimage_eq_of_le hW).le s)
  have he' := congrArg (res (image_preimage_eq_of_le (h.trans hW)).symm.le) he
  simpa only [moduleRes_comp, res_comp] using he'

theorem localFrameCoordinates_symm_restrict {U V W : X.Opens}
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ W) (hW : W ≤ U) (r : Γ(X, W)) :
    moduleRes M h ((localFrameCoordinates M e W hW).symm r) =
      (localFrameCoordinates M e V (h.trans hW)).symm (res h r) := by
  apply (localFrameCoordinates M e V (h.trans hW)).injective
  rw [localFrameCoordinates_restrict M e h hW, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end ArithDyn.Extension.ProjTwist
