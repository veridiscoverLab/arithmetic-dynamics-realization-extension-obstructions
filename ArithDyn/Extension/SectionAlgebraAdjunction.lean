import ArithDyn.Extension.SectionAlgebraMaps

/-! # Concrete adjunction transport identities for section pullback -/
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace ArithDyn.Extension.SectionAlgebra
set_option backward.isDefEq.respectTransparency false
noncomputable section

section Category
variable {A : Type u} {B : Type v} [Category A] [Category B]
variable {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}

/-- Moving a left-adjoint comparison across the adjunction produces its actual mate. -/
theorem homEquiv_conjugate_postcomp (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (e : L₂ ⟶ L₁) {M : A} {N : B} (h : L₁.obj M ⟶ N) :
    a₂.homEquiv M N (e.app M ≫ h) =
      a₁.homEquiv M N h ≫ (conjugateEquiv a₁ a₂ e).app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← unit_conjugateEquiv, Category.assoc,
    ← NatTrans.naturality, ← Category.assoc]

end Category

variable {X Y Z : Scheme.{u}}

/-- The actual composite pullback adjoint equals the two original adjoints,
with the canonical pushforward comparison. -/
theorem adjoint_pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} {N : X.Modules}
    (α : (Modules.pullback f).obj ((Modules.pullback g).obj M) ⟶ N) :
    (Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv M N
        ((Modules.pullbackComp f g).inv.app M ≫ α) =
      ((Modules.pullbackPushforwardAdjunction g).comp
        (Modules.pullbackPushforwardAdjunction f)).homEquiv M N α ≫
          (Modules.pushforwardComp f g).hom.app N := by
  rw [homEquiv_conjugate_postcomp, Modules.conjugateEquiv_pullbackComp_inv]

/-- The concrete restriction adjoint and abstract inverse-image adjoint agree
under the canonical uniqueness isomorphism. -/
theorem adjoint_restrictIso (f : X ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} {N : X.Modules}
    (α : (Modules.pullback f).obj M ⟶ N) :
    (Modules.restrictAdjunction f).homEquiv M N
      ((Modules.restrictFunctorIsoPullback f).hom.app M ≫ α) =
        (Modules.pullbackPushforwardAdjunction f).homEquiv M N α := by
  rw [Adjunction.homEquiv_naturality_right]
  rw [Modules.restrictFunctorIsoPullback, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

end
end ArithDyn.Extension.SectionAlgebra
