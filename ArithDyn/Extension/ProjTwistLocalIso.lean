import ArithDyn.Extension.ProjTwistLocal
import Mathlib.Topology.Sheaves.Stalks

/-! # Detection of actual module isomorphisms on an open cover -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.Scheme

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{u}}

private theorem isIso_map_iff_of_natIso {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (e : F ≅ G) {a b : A} (f : a ⟶ b) :
    IsIso (F.map f) ↔ IsIso (G.map f) := by
  rw [← isIso_comp_right_iff (F.map f) (e.hom.app b), e.hom.naturality,
    isIso_comp_left_iff]

/-- All local restrictions together detect an isomorphism of actual sheaves of modules. -/
theorem isIso_of_restrictions {ι : Type v} (U : ι → X.Opens)
    (hcover : iSup U = ⊤) {M N : X.Modules} (α : M ⟶ N)
    (hα : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map α)) : IsIso α := by
  apply (isIso_iff_of_reflects_iso α (Scheme.Modules.toPresheaf X)).mp
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  let G : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let β : F ⟶ G := ⟨α.mapPresheaf⟩
  have hβ : IsIso β := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso β).mpr
    intro x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by
      apply TopologicalSpace.Opens.mem_iSup.mp
      rw [hcover]
      trivial
    let y : (U i).toScheme := ⟨x, hi⟩
    let e := Scheme.Modules.restrictStalkNatIso (U i).ι y
    haveI := hα i
    change IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map α.mapPresheaf)
    exact (isIso_map_iff_of_natIso e α).mp (by
      dsimp [e]
      exact (TopCat.Presheaf.stalkFunctor Ab y).map_isIso
        ((Scheme.Modules.toPresheaf (U i).toScheme).map
          ((Scheme.Modules.restrictFunctor (U i).ι).map α)))
  exact (TopCat.Sheaf.forget Ab X).map_isIso β

end ArithDyn.Extension.ProjTwist
