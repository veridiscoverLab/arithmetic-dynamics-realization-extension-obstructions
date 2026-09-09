import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Section maps from actual pullback morphisms of scheme modules

The maps in this file are derived from the actual pullback-pushforward
adjunction on `Scheme.Modules`.  A sheaf morphism `f⁎ M ⟶ N` supplies a
semilinear map on sections on every open, compatible with restrictions.
In particular a polarization isomorphism supplies its section map, rather
than requiring that map as a separate field.  No identification of
`Γ(X, ⊤)` with a ground field is made.
-/

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme

namespace ArithDyn.Extension.SectionAlgebra

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable {M : Y.Modules} {N P : X.Modules}

/-- The actual adjoint sheaf morphism associated to a pullback morphism. -/
def adjoint (α : (Modules.pullback f).obj M ⟶ N) :
    M ⟶ (Modules.pushforward f).obj N :=
  (Modules.pullbackPushforwardAdjunction f).homEquiv _ _ α

/-- A pullback sheaf morphism gives the actual semilinear map on sections. -/
def mapOnSections (α : (Modules.pullback f).obj M ⟶ N) (U : Y.Opens) :
    Γ(M, U) →ₛₗ[(f.app U).hom] Γ(N, f ⁻¹ᵁ U) where
  toFun := (adjoint f α).app U
  map_add' := ((adjoint f α).app U).hom.map_add
  map_smul' r x := (adjoint f α).app_smul r x

@[simp] theorem mapOnSections_apply (α : (Modules.pullback f).obj M ⟶ N)
    (U : Y.Opens) (x : Γ(M, U)) :
    mapOnSections f α U x = (adjoint f α).app U x := rfl

/-- The adjunction construction commutes with actual sheaf restrictions. -/
theorem mapOnSections_restrict (α : (Modules.pullback f).obj M ⟶ N)
    {U V : Y.Opens} (i : U ⟶ V) (x : Γ(M, V)) :
    N.presheaf.map ((Opens.map f.base).map i).op (mapOnSections f α V x) =
      mapOnSections f α U (M.presheaf.map i.op x) := by
  exact congrArg (fun h => h x) ((adjoint f α).mapPresheaf.naturality i.op).symm

/-- Postcomposition of pullback morphisms is respected on every open. -/
theorem mapOnSections_comp (α : (Modules.pullback f).obj M ⟶ N) (β : N ⟶ P)
    (U : Y.Opens) (x : Γ(M, U)) :
    mapOnSections f (α ≫ β) U x = β.app (f ⁻¹ᵁ U) (mapOnSections f α U x) := by
  have hα : adjoint f (α ≫ β) = adjoint f α ≫ (Modules.pushforward f).map β :=
    (Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right α β
  exact congrArg (fun γ => γ.app U x) hα

/-- Pullback itself is obtained by applying the unit of the actual adjunction. -/
def pullbackOnSections (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) →ₛₗ[(f.app U).hom] Γ((Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  mapOnSections f (𝟙 _) U

theorem mapOnSections_eq_pullback (α : (Modules.pullback f).obj M ⟶ N)
    (U : Y.Opens) (x : Γ(M, U)) :
    mapOnSections f α U x = α.app (f ⁻¹ᵁ U) (pullbackOnSections f M U x) := by
  simpa [pullbackOnSections] using mapOnSections_comp f (𝟙 _) α U x

/-- The map induced by an actual polarization isomorphism of sheaves. -/
def polarizedOnSections (e : (Modules.pullback f).obj M ≅ N) (U : Y.Opens) :
    Γ(M, U) →ₛₗ[(f.app U).hom] Γ(N, f ⁻¹ᵁ U) :=
  mapOnSections f e.hom U

/-- A polarization isomorphism neither creates nor erases a zero after pullback. -/
theorem polarizedOnSections_eq_zero_iff (e : (Modules.pullback f).obj M ≅ N)
    (U : Y.Opens) (x : Γ(M, U)) :
    polarizedOnSections f e U x = 0 ↔ pullbackOnSections f M U x = 0 := by
  change mapOnSections f e.hom U x = 0 ↔ _
  rw [mapOnSections_eq_pullback]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (e.hom.app (f ⁻¹ᵁ U))).1

section Base

variable {k : Type u} [CommRing k]

/-- Constants on an actual scheme over `Spec k`, retaining its full global ring. -/
def baseRingHom (p : X ⟶ Spec (CommRingCat.of k)) : k →+* Γ(X, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- The action of an actual morphism over `Spec k` fixes the corresponding constants. -/
theorem baseRingHom_naturality
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    (h : f ≫ pY = pX) :
    f.appTop.hom.comp (baseRingHom pY) = baseRingHom pX := by
  rw [baseRingHom, baseRingHom, ← RingHom.comp_assoc]
  change ((f ≫ pY).appTop).hom.comp _ = _
  rw [h]

/-- Actual global sections as a module over the ground ring, without requiring
that every global function is a constant. -/
def globalSectionsOver (p : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) : ModuleCat k :=
  letI := Module.compHom Γ(M, ⊤) (baseRingHom p)
  ModuleCat.of k Γ(M, ⊤)

/-- Ground-ring linearity follows from the actual base-morphism equation. -/
def mapOnGlobalSectionsOver
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    (h : f ≫ pY = pX) (α : (Modules.pullback f).obj M ⟶ N) :
    globalSectionsOver pY M →ₗ[k] globalSectionsOver pX N where
  toFun := mapOnSections f α ⊤
  map_add' := map_add (mapOnSections f α ⊤)
  map_smul' c x := by
    have hsm := (mapOnSections f α ⊤).map_smulₛₗ (baseRingHom pY c) x
    have hc : (f.app ⊤).hom (baseRingHom pY c) = baseRingHom pX c :=
      RingHom.congr_fun (baseRingHom_naturality f pX pY h) c
    rw [hc] at hsm
    exact hsm

end Base

end

end ArithDyn.Extension.SectionAlgebra
