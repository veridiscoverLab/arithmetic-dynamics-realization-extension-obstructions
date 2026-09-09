import ArithDyn.Extension.ProjTwistLocalIso

/-! # Local bases of the actual inverse-image module -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace ArithDyn.Extension.ProjTwist

variable {X Y : Scheme.{u}}

/-- Inverse image of opens is final: every comma category has the terminal full open. -/
instance opensMapFinal (f : X ⟶ Y) : (Opens.map f.base).Final where
  out V := by
    let T : StructuredArrow V (Opens.map f.base) :=
      StructuredArrow.mk (homOfLE (show V ≤ (Opens.map f.base).obj ⊤ from le_top))
    apply isConnected_of_isTerminal (StructuredArrow V (Opens.map f.base)) (x := T)
    refine IsTerminal.ofUniqueHom (fun A => ?_) ?_
    · refine StructuredArrow.homMk (homOfLE le_top) ?_
      apply Subsingleton.elim
    · intro A g
      apply StructuredArrow.hom_ext
      apply Subsingleton.elim

/-- The standard inverse-image functor takes the unit module to the unit module. -/
def pullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  by
    letI : (Opens.map f.base).Final := opensMapFinal f
    exact asIso (C := SheafOfModules X.ringCatSheaf)
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

variable {X Y : Scheme.{max u v}} {ι : Type v}

/-- A local basis of the actual inverse image, built from functorial pullback and the
original local basis.  No pullback-line-bundle isomorphism is assumed. -/
def inverseImageLocalIso (f : X ⟶ Y) (C : UnitCocycle Y ι) (n : ℕ) (i : ι) :
    (Scheme.Modules.pullback (f ⁻¹ᵁ C.cover i).ι).obj
      ((Scheme.Modules.pullback f).obj (twistedModule C n)) ≅
        SheafOfModules.unit (f ⁻¹ᵁ C.cover i).toScheme.ringCatSheaf :=
  (Scheme.Modules.pullbackComp (f ⁻¹ᵁ C.cover i).ι f).app (twistedModule C n) ≪≫
    (Scheme.Modules.pullbackCongr (f.resLE_comp_ι (U := C.cover i) le_rfl).symm).app
      (twistedModule C n) ≪≫
    ((Scheme.Modules.pullbackComp (f.resLE (C.cover i) (f ⁻¹ᵁ C.cover i) le_rfl)
      (C.cover i).ι).app (twistedModule C n)).symm ≪≫
    (Scheme.Modules.pullback (f.resLE (C.cover i) (f ⁻¹ᵁ C.cover i) le_rfl)).mapIso
      (localPullbackIso C n i (C.cover i) le_rfl) ≪≫
    pullbackUnitIso (f.resLE (C.cover i) (f ⁻¹ᵁ C.cover i) le_rfl)

/-- The same basis, expressed using the concrete restriction functor. -/
def inverseImageRestrictionIso (f : X ⟶ Y) (C : UnitCocycle Y ι) (n : ℕ) (i : ι) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback f).obj (twistedModule C n))
      (f ⁻¹ᵁ C.cover i).ι ≅
        SheafOfModules.unit (f ⁻¹ᵁ C.cover i).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ C.cover i).ι).app
    ((Scheme.Modules.pullback f).obj (twistedModule C n)) ≪≫
      inverseImageLocalIso f C n i

end ArithDyn.Extension.ProjTwist
