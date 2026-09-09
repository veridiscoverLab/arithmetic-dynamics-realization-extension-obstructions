import ArithDyn.Extension.SectionAlgebraSheaf

/-!
# Actual pullback on all degrees of cocycle section algebras

Every coefficient is pulled back by the same scheme morphism.  The transition
units, the full overlap relations, the module-sheaf morphism, and multiplication
are constructed from its actual maps on regular functions.
-/

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace DirectSum Opposite

namespace ArithDyn.Extension.ProjTwist

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type v} (C : UnitCocycle Y ι)

/-- The actual map on regular functions with an arbitrary source restriction. -/
abbrev pullRegular {U : Y.Opens} {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U) :
    Γ(Y, U) →+* Γ(X, V) := (f.appLE U V h).hom

@[simp] theorem res_pullRegular {U : Y.Opens} {V W : X.Opens}
    (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U) (s : Γ(Y, U)) :
    res h (pullRegular f hW s) = pullRegular f (h.trans hW) s := by
  exact congrArg (fun z => z s) (f.appLE_map hW (homOfLE h).op)

@[simp] theorem pullRegular_res {U W : Y.Opens} {V : X.Opens}
    (h : U ≤ W) (hV : V ≤ f ⁻¹ᵁ U) (s : Γ(Y, W)) :
    pullRegular f hV (res h s) =
      pullRegular f (hV.trans ((Opens.map f.base).map (homOfLE h)).le) s := by
  exact congrArg (fun z => z s) (f.map_appLE hV (homOfLE h).op)

/-- Pull a transition unit back from the common chart intersection. -/
def pulledTransition (i j : ι) (V : X.Opens)
    (hi : V ≤ f ⁻¹ᵁ C.cover i) (hj : V ≤ f ⁻¹ᵁ C.cover j) : Γ(X, V)ˣ :=
  Units.map (pullRegular f (le_inf hi hj)).toMonoidHom
    (C.g i j (C.cover i ⊓ C.cover j) inf_le_left inf_le_right)

/-- The same transition may be computed on any smaller target intersection. -/
theorem pulledTransition_eq (i j : ι) (U : Y.Opens) (V : X.Opens)
    (hi : U ≤ C.cover i) (hj : U ≤ C.cover j) (hV : V ≤ f ⁻¹ᵁ U) :
    pulledTransition f C i j V
        (hV.trans ((Opens.map f.base).map (homOfLE hi)).le)
        (hV.trans ((Opens.map f.base).map (homOfLE hj)).le) =
      Units.map (pullRegular f hV).toMonoidHom (C.g i j U hi hj) := by
  apply Units.ext
  change pullRegular f _ (C.g i j (C.cover i ⊓ C.cover j) inf_le_left inf_le_right : Γ(Y, C.cover i ⊓ C.cover j)) =
    pullRegular f hV (C.g i j U hi hj : Γ(Y, U))
  rw [← res_g C i j (le_inf hi hj) inf_le_left inf_le_right, pullRegular_res]

def pullbackCocycle : UnitCocycle X ι where
  cover i := f ⁻¹ᵁ C.cover i
  covers := by
    exact f.iSup_preimage_eq_top C.covers
  g := pulledTransition f C
  naturality i j V W h hi hj := by
    apply Units.ext
    exact res_pullRegular f (U := C.cover i ⊓ C.cover j) h (le_inf hi hj) _
  self i V hi := by
    rw [pulledTransition_eq f C i i (C.cover i) V le_rfl le_rfl hi, C.self]
    exact map_one _
  comp i j k V hi hj hk := by
    let U : Y.Opens := C.cover i ⊓ C.cover j ⊓ C.cover k
    have hU : V ≤ f ⁻¹ᵁ U := le_inf (le_inf hi hj) hk
    rw [pulledTransition_eq f C i j U V (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) hU,
      pulledTransition_eq f C j k U V (inf_le_left.trans inf_le_right) inf_le_right hU,
      pulledTransition_eq f C i k U V (inf_le_left.trans inf_le_left) inf_le_right hU,
      ← map_mul, C.comp]

@[simp] theorem pullbackCocycle_cover (i : ι) :
    (pullbackCocycle f C).cover i = f ⁻¹ᵁ C.cover i := rfl

/-- The coefficientwise pullback on every open and homogeneous degree. -/
def pullbackSections (n : ℕ) (V : Y.Opens) (a : TwistedSections C n V) :
    TwistedSections (pullbackCocycle f C) n (f ⁻¹ᵁ V) := by
  refine ⟨fun i => pullRegular f (le_refl (f ⁻¹ᵁ (V ⊓ C.cover i))) (a.1 i), ?_⟩
  intro i j
  have ha := congrArg (pullRegular f (le_refl (f ⁻¹ᵁ overlap C V i j))) (a.2 i j)
  have hg := pulledTransition_eq f C i j (overlap C V i j)
    (overlap (pullbackCocycle f C) (f ⁻¹ᵁ V) i j)
    (inf_le_left.trans inf_le_right) inf_le_right le_rfl
  change (pullbackCocycle f C).g i j _ (inf_le_left.trans inf_le_right) inf_le_right = _ at hg
  rw [hg]
  change res (f.preimage_mono (inf_le_left : overlap C V i j ≤ V ⊓ C.cover i))
      (pullRegular f le_rfl (a.1 i)) =
    (pullRegular f le_rfl (C.g i j (overlap C V i j)
      (inf_le_left.trans inf_le_right) inf_le_right : Γ(Y, overlap C V i j))) ^ n *
    res (f.preimage_mono (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      overlap C V i j ≤ V ⊓ C.cover j)) (pullRegular f le_rfl (a.1 j))
  simpa only [map_mul, map_pow, pullRegular_res, res_pullRegular] using ha

@[simp] theorem pullbackSections_apply (n : ℕ) (V : Y.Opens)
    (a : TwistedSections C n V) (i : ι) :
    (pullbackSections f C n V a).1 i = pullRegular f le_rfl (a.1 i) := rfl

@[simp] theorem pullbackSections_restrict (n : ℕ) {V W : Y.Opens} (h : V ≤ W)
    (a : TwistedSections C n W) :
    pullbackSections f C n V (restrictSections C n h a) =
      restrictSections (pullbackCocycle f C) n
        (((Opens.map f.base).map (homOfLE h)).le) (pullbackSections f C n W a) := by
  ext i
  exact (pullRegular_res f (inf_le_inf h le_rfl) le_rfl (a.1 i)).trans
    (res_pullRegular f _ le_rfl (a.1 i)).symm

/-- Every actual coefficient pullback is semilinear over the same `f.app V`. -/
theorem pullbackSections_smul (n : ℕ) (V : Y.Opens)
    (r : Γ(Y, V)) (a : TwistedSections C n V) :
    pullbackSections f C n V (r • a) =
      (f.app V).hom r • pullbackSections f C n V a := by
  ext i
  change pullRegular f le_rfl (res inf_le_left r * a.1 i) =
    res (f.preimage_mono (inf_le_left : V ⊓ C.cover i ≤ V)) ((f.app V).hom r) * pullRegular f le_rfl (a.1 i)
  rw [map_mul, pullRegular_res]
  rw [← Scheme.Hom.appLE_eq_app f, res_pullRegular]

/-- All degrees commute with actual multiplication on chart coefficients. -/
theorem pullbackSections_mul {n m : ℕ} (V : Y.Opens)
    (a : TwistedSections C n V) (b : TwistedSections C m V) :
    pullbackSections f C (n + m) V (SectionAlgebra.mulSections C a b) =
      SectionAlgebra.mulSections (pullbackCocycle f C)
        (pullbackSections f C n V a) (pullbackSections f C m V b) := by
  ext i
  exact map_mul _ _ _

/-- The actual ring map on the complete algebra, simultaneously for all degrees. -/
def sectionAlgebraPullback (V : Y.Opens) :
    SectionAlgebra.sectionAlgebraOn C V →+*
      SectionAlgebra.sectionAlgebraOn (pullbackCocycle f C) (f ⁻¹ᵁ V) :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of (fun n => ↥(TwistedSections (pullbackCocycle f C) n
      (f ⁻¹ᵁ V))) n).comp
      { toFun := pullbackSections f C n V
        map_zero' := by ext i; exact map_zero _
        map_add' a b := by ext i; exact map_add _ _ _ })
    (by
      change DirectSum.of (fun n => ↥(TwistedSections (pullbackCocycle f C) n
        (f ⁻¹ᵁ V))) 0 (pullbackSections f C 0 V ⟨1, SectionAlgebra.compatible_one C V⟩) = 1
      have h : pullbackSections f C 0 V ⟨1, SectionAlgebra.compatible_one C V⟩ =
          (⟨1, SectionAlgebra.compatible_one (pullbackCocycle f C) (f ⁻¹ᵁ V)⟩ :
            TwistedSections (pullbackCocycle f C) 0 (f ⁻¹ᵁ V)) := by
        ext i
        exact map_one _
      rw [h]
      rfl)
    (by
      intro n m a b
      change DirectSum.of (fun n => ↥(TwistedSections (pullbackCocycle f C) n
        (f ⁻¹ᵁ V))) (n + m)
          (pullbackSections f C (n + m) V (SectionAlgebra.mulSections C a b)) =
        DirectSum.of (fun n => ↥(TwistedSections (pullbackCocycle f C) n (f ⁻¹ᵁ V))) n
          (pullbackSections f C n V a) *
        DirectSum.of (fun n => ↥(TwistedSections (pullbackCocycle f C) n (f ⁻¹ᵁ V))) m
          (pullbackSections f C m V b)
      rw [DirectSum.of_mul_of, pullbackSections_mul]
      rfl)

@[simp] theorem sectionAlgebraPullback_of (V : Y.Opens) (n : ℕ)
    (a : TwistedSections C n V) :
    sectionAlgebraPullback f C V (DirectSum.of (fun n => ↥(TwistedSections C n V)) n a) =
      DirectSum.of (fun n => ↥(TwistedSections (pullbackCocycle f C) n (f ⁻¹ᵁ V))) n
        (pullbackSections f C n V a) := by
  simp only [sectionAlgebraPullback, DirectSum.toSemiring_of]
  rfl

/-- Naturality holds for the full section algebra, not only for each fixed degree. -/
theorem sectionAlgebraPullback_restrict {V W : Y.Opens} (h : V ≤ W) :
    (sectionAlgebraPullback f C V).comp (SectionAlgebra.sectionRestriction C h) =
      (SectionAlgebra.sectionRestriction (pullbackCocycle f C)
        (((Opens.map f.base).map (homOfLE h)).le)).comp (sectionAlgebraPullback f C W) := by
  apply DirectSum.ringHom_ext
  intro n a
  simp only [RingHom.comp_apply, SectionAlgebra.sectionRestriction_of,
    sectionAlgebraPullback_of, pullbackSections_restrict]

end

noncomputable section SheafHom

variable {X Y : Scheme.{max u v}} (f : X ⟶ Y) {ι : Type v} (C : UnitCocycle Y ι)

/-- The actual morphism of module sheaves adjoint to pullback.  Its value on each
open is exactly the same coefficientwise map used by the graded ring map. -/
def pullbackSectionsHom (n : ℕ) :
    (twistedModule C n : Y.Modules) ⟶
      (Scheme.Modules.pushforward f).obj (twistedModule (pullbackCocycle f C) n) where
  val := PresheafOfModules.homMk {
    app := fun V => AddCommGrpCat.ofHom {
      toFun := pullbackSections f C n V.unop
      map_zero' := by apply Subtype.ext; funext i; exact map_zero _
      map_add' a b := by apply Subtype.ext; funext i; exact map_add _ _ _ }
    naturality := fun {V W} h => by
      ext a
      exact pullbackSections_restrict f C n h.unop.le a }
    (fun V r a => pullbackSections_smul f C n V.unop r a)

@[simp] theorem pullbackSectionsHom_app (n : ℕ) (V : Y.Opens)
    (a : TwistedSections C n V) :
    Scheme.Modules.Hom.app (pullbackSectionsHom f C n) V a = pullbackSections f C n V a := rfl

end SheafHom

end ArithDyn.Extension.ProjTwist
