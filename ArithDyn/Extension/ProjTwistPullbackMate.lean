import ArithDyn.Extension.ProjTwistPullback
import ArithDyn.Extension.SectionAlgebraAdjunction

/-! # The local adjunction square for canonical cocycle pullback -/
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace
namespace ArithDyn.Extension.ProjTwist
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section

private theorem compAdjunction_homEquiv_apply
    {A B D : Type*} [Category A] [Category B] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ D} {R₂ : D ⥤ B}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (M : A) (N : D)
    (h : L₂.obj (L₁.obj M) ⟶ N) :
    (a₁.comp a₂).homEquiv M N h = a₁.homEquiv M _ (a₂.homEquiv _ N h) := by
  rw [Adjunction.comp_homEquiv]
  rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The chosen unit pullback is the adjoint of the actual regular-function map. -/
theorem pullbackUnitIso_adjoint (g : X ⟶ Y) :
    (Modules.pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    g.toRingCatSheafHom

/-- The actual commutative square identifies its two composite pushforwards. -/
def localPushforwardIso :
    Modules.pushforward (f.resLE U (f ⁻¹ᵁ U) le_rfl) ⋙ Modules.pushforward U.ι ≅
      Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Modules.pushforward f :=
  (Modules.pushforwardComp (f.resLE U (f ⁻¹ᵁ U) le_rfl) U.ι) ≪≫
    Modules.pushforwardCongr (f.resLE_comp_ι (U := U) le_rfl) ≪≫
    (Modules.pushforwardComp (f ⁻¹ᵁ U).ι f).symm

/-- Its mate is a genuine isomorphism of the two local pullback functors. -/
def localPullbackMateIso :
    Modules.pullback f ⋙ Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Modules.restrictFunctor U.ι ⋙ Modules.pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) :=
  (conjugateIsoEquiv
    ((Modules.restrictAdjunction U.ι).comp
      (Modules.pullbackPushforwardAdjunction (f.resLE U (f ⁻¹ᵁ U) le_rfl)))
    ((Modules.pullbackPushforwardAdjunction f).comp
      (Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))).symm (localPushforwardIso f U)

/-- The comparison is defined by the actual right-adjoint square. -/
theorem localPullbackMateIso_adjoint
    {M : Y.Modules} {N : (f ⁻¹ᵁ U).toScheme.Modules}
    (α : (Modules.pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl)).obj
      ((Modules.restrictFunctor U.ι).obj M) ⟶ N) :
    ((Modules.pullbackPushforwardAdjunction f).comp
      (Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)).homEquiv M N
        ((localPullbackMateIso f U).hom.app M ≫ α) =
      ((Modules.restrictAdjunction U.ι).comp
        (Modules.pullbackPushforwardAdjunction (f.resLE U (f ⁻¹ᵁ U) le_rfl))).homEquiv M N α ≫
          (localPushforwardIso f U).hom.app N := by
  rw [SectionAlgebra.homEquiv_conjugate_postcomp]
  congr 1
  change (conjugateIsoEquiv _ _ ((conjugateIsoEquiv _ _).symm
    (localPushforwardIso f U))).hom.app N = _
  rw [Equiv.apply_symm_apply]

end

noncomputable section

variable {X Y : Scheme.{max u v}} (f : X ⟶ Y) {ι : Type v} (C : UnitCocycle Y ι)

/-- A local trivialization of the actual inverse image, using the same adjunction square. -/
def mateLocalIso (n : ℕ) (i : ι) :
    Modules.restrict ((Modules.pullback f).obj (twistedModule C n))
      (f ⁻¹ᵁ C.cover i).ι ≅
        SheafOfModules.unit (f ⁻¹ᵁ C.cover i).toScheme.ringCatSheaf :=
  (localPullbackMateIso f (C.cover i)).app (twistedModule C n) ≪≫
    (Modules.pullback (f.resLE (C.cover i) (f ⁻¹ᵁ C.cover i) le_rfl)).mapIso
      (localRestrictionIso C n i (C.cover i) le_rfl) ≪≫
    pullbackUnitIso (f.resLE (C.cover i) (f ⁻¹ᵁ C.cover i) le_rfl)

/-- The original coefficientwise map and the two local basis maps form the
actual commutative right-adjoint square. -/
theorem local_basis_adjoint_square (n : ℕ) (i : ι) :
    pullbackSectionsHom f C n ≫
      (Modules.pushforward f).map
        ((Modules.restrictAdjunction (f ⁻¹ᵁ C.cover i).ι).homEquiv _ _
          (localRestrictionIso (pullbackCocycle f C) n i (f ⁻¹ᵁ C.cover i) le_rfl).hom) =
      (Modules.restrictAdjunction (C.cover i).ι).homEquiv _ _
        ((localRestrictionIso C n i (C.cover i) le_rfl).hom ≫
          SheafOfModules.unitToPushforwardObjUnit
            (f.resLE (C.cover i) (f ⁻¹ᵁ C.cover i) le_rfl).toRingCatSheafHom) ≫
        (localPushforwardIso f (C.cover i)).hom.app _ := by
  apply Modules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro a
  simp only [Adjunction.homEquiv_unit, Modules.Hom.comp_app,
    Modules.pushforward_map_app, Modules.restrictAdjunction_unit_app_app]
  dsimp only [Modules.Hom.app, Modules.pushforward, SheafOfModules.comp_val,
    PresheafOfModules.comp_app]
  change res (le_inf le_rfl ((f ⁻¹ᵁ C.cover i).ι_image_le
      ((f ⁻¹ᵁ C.cover i).ι ⁻¹ᵁ (f ⁻¹ᵁ V))))
      (res (inf_le_inf ((f ⁻¹ᵁ C.cover i).ι.image_preimage_le (f ⁻¹ᵁ V)) le_rfl)
        (pullRegular f le_rfl (a.1 i))) = _
  rw [res_comp]
  erw [res_pullRegular]
  have hpre : (f ⁻¹ᵁ C.cover i).ι ⁻¹ᵁ (f ⁻¹ᵁ V) ≤
      (f.resLE (C.cover i) (f ⁻¹ᵁ C.cover i) le_rfl) ⁻¹ᵁ ((C.cover i).ι ⁻¹ᵁ V) := by
    rw [← Hom.comp_preimage, ← Hom.comp_preimage, f.resLE_comp_ι]
  change _ = ((f.resLE (C.cover i) (f ⁻¹ᵁ C.cover i) le_rfl).appLE
    ((C.cover i).ι ⁻¹ᵁ V) ((f ⁻¹ᵁ C.cover i).ι ⁻¹ᵁ (f ⁻¹ᵁ V)) hpre).hom
      (toLocal C n i ((C.cover i).ι ''ᵁ ((C.cover i).ι ⁻¹ᵁ V))
        ((C.cover i).ι_image_le _) (restrictSections C n ((C.cover i).ι.image_preimage_le V) a))
  rw [Hom.resLE_appLE]
  change _ = pullRegular f _ (res _ (res _ (a.1 i)))
  rw [res_comp, pullRegular_res]


/-- In the actual local bases the canonical comparison is the identity map. -/
theorem pullbackComparison_local_identity (n : ℕ) (i : ι) :
    (Modules.restrictFunctor (f ⁻¹ᵁ C.cover i).ι).map (pullbackComparison f C n) ≫
      (localRestrictionIso (pullbackCocycle f C) n i (f ⁻¹ᵁ C.cover i) le_rfl).hom =
        (mateLocalIso f C n i).hom := by
  apply (((Modules.pullbackPushforwardAdjunction f).comp
    (Modules.restrictAdjunction (f ⁻¹ᵁ C.cover i).ι)).homEquiv _ _).injective
  change _ = ((Modules.pullbackPushforwardAdjunction f).comp
    (Modules.restrictAdjunction (f ⁻¹ᵁ C.cover i).ι)).homEquiv _ _
      ((localPullbackMateIso f (C.cover i)).hom.app (twistedModule C n) ≫
        (Modules.pullback (f.resLE (C.cover i) (f ⁻¹ᵁ C.cover i) le_rfl)).map
          (localRestrictionIso C n i (C.cover i) le_rfl).hom ≫
            (pullbackUnitIso (f.resLE (C.cover i) (f ⁻¹ᵁ C.cover i) le_rfl)).hom)
  rw [localPullbackMateIso_adjoint]
  rw [compAdjunction_homEquiv_apply, compAdjunction_homEquiv_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackComparison_adjoint, Adjunction.homEquiv_naturality_left]
  rw [pullbackUnitIso_adjoint]
  set_option backward.isDefEq.respectTransparency true in
    exact local_basis_adjoint_square.{u, v} (X := X) (Y := Y) f C n i

/-- The canonical comparison is locally the constructed isomorphism and hence
is an actual isomorphism of module sheaves globally. -/
instance pullbackComparison_isIso (n : ℕ) : IsIso (pullbackComparison f C n) := by
  apply isIso_of_restrictions (fun i => f ⁻¹ᵁ C.cover i)
    (f.iSup_preimage_eq_top C.covers) (pullbackComparison f C n)
  intro i
  have h := pullbackComparison_local_identity f C n i
  have hi : IsIso ((Modules.restrictFunctor (f ⁻¹ᵁ C.cover i).ι).map
      (pullbackComparison f C n) ≫
        (localRestrictionIso (pullbackCocycle f C) n i (f ⁻¹ᵁ C.cover i) le_rfl).hom) := by
    rw [h]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

/-- Actual inverse image of the original cocycle sheaf, canonically identified
with the sheaf constructed from the pulled transition units. -/
def pullbackTwistedIso (n : ℕ) :
    (Modules.pullback f).obj (twistedModule C n) ≅
      twistedModule (pullbackCocycle f C) n :=
  asIso (pullbackComparison f C n)

@[simp] theorem pullbackTwistedIso_hom (n : ℕ) :
    (pullbackTwistedIso f C n).hom = pullbackComparison f C n := rfl

end
end ArithDyn.Extension.ProjTwist
