import ArithDyn.Extension.SectionAlgebraCocycle
import ArithDyn.Extension.ProjTwistSheaf

/-!
# The graded algebra of sections of actual cocycle sheaves

The sheaves here are proved to satisfy gluing in the original structure sheaf.
Their values, the section algebra, and its restrictions are actual constructions.
-/

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace DirectSum
open ArithDyn.Extension.ProjTwist

namespace ArithDyn.Extension.SectionAlgebra

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {X : Scheme.{u}} {ι : Type v} (C : UnitCocycle X ι)

/-- The direct sum of the actual values of the proved sheaves of modules. -/
abbrev sheafSectionAlgebraOn (V : X.Opens) :=
  ⨁ n : ℕ, ((twistedModule C n).val.obj (.op V))

/-- This is the same algebra of matching families, not merely an abstract model. -/
theorem sheafSectionAlgebraOn_eq (V : X.Opens) :
    sheafSectionAlgebraOn C V = sectionAlgebraOn C V := rfl

/-- The actual restriction of each homogeneous degree, bundled additively. -/
def sectionRestrictionAddHom (n : ℕ) {V W : X.Opens} (h : V ≤ W) :
    TwistedSections C n W →+ TwistedSections C n V where
  toFun := restrictSections C n h
  map_zero' := by ext i; exact map_zero _
  map_add' a b := by ext i; exact map_add _ _ _

/-- Restrictions respect the degree-changing multiplication proved on all overlaps. -/
theorem restrict_mulSections {n m : ℕ} {V W : X.Opens} (h : V ≤ W)
    (a : TwistedSections C n W) (b : TwistedSections C m W) :
    restrictSections C (n + m) h (mulSections C a b) =
      mulSections C (restrictSections C n h a) (restrictSections C m h b) := by
  ext i
  exact map_mul _ _ _

/-- The actual ring restriction on the full section algebra. -/
def sectionRestriction {V W : X.Opens} (h : V ≤ W) :
    sectionAlgebraOn C W →+* sectionAlgebraOn C V :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of (fun n => ↥(TwistedSections C n V)) n).comp
      (sectionRestrictionAddHom C n h))
    (by
      change DirectSum.of (fun n => ↥(TwistedSections C n V)) 0
        (restrictSections C 0 h ⟨1, compatible_one C W⟩) = 1
      have hz : restrictSections C 0 h ⟨1, compatible_one C W⟩ =
          (⟨1, compatible_one C V⟩ : TwistedSections C 0 V) := by
        ext i
        exact map_one _
      rw [hz]
      rfl)
    (by
      intro n m a b
      change DirectSum.of (fun n => ↥(TwistedSections C n V)) (n + m)
        (restrictSections C (n + m) h (mulSections C a b)) =
        DirectSum.of (fun n => ↥(TwistedSections C n V)) n (restrictSections C n h a) *
          DirectSum.of (fun n => ↥(TwistedSections C n V)) m (restrictSections C m h b)
      rw [DirectSum.of_mul_of, restrict_mulSections]
      rfl)

@[simp] theorem sectionRestriction_of {V W : X.Opens} (h : V ≤ W)
    (n : ℕ) (a : TwistedSections C n W) :
    sectionRestriction C h (DirectSum.of (fun n => ↥(TwistedSections C n W)) n a) =
      DirectSum.of (fun n => ↥(TwistedSections C n V)) n (restrictSections C n h a) := by
  simp [sectionRestriction, sectionRestrictionAddHom]

theorem sectionRestriction_refl (V : X.Opens) :
    sectionRestriction C (le_refl V) = RingHom.id _ := by
  apply DirectSum.ringHom_ext
  intro n a
  simp

theorem sectionRestriction_comp {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) :
    (sectionRestriction C hUV).comp (sectionRestriction C hVW) =
      sectionRestriction C (hUV.trans hVW) := by
  apply DirectSum.ringHom_ext
  intro n a
  simp

/-- Degree zero is supplied by restrictions of actual regular functions. -/
def zeroSection (V : X.Opens) (s : Γ(X, V)) : TwistedSections C 0 V := by
  refine ⟨fun i => res (inf_le_left : V ⊓ C.cover i ≤ V) s, ?_⟩
  intro i j
  simp [res_comp]

@[simp] theorem zeroSection_apply (V : X.Opens) (s : Γ(X, V)) (i : ι) :
    (zeroSection C V s).1 i = res inf_le_left s := rfl

theorem cover_intersection (V : X.Opens) : V ≤ ⨆ i, V ⊓ C.cover i := by
  rw [← inf_iSup_eq, C.covers, inf_top_eq]

/-- Actual sheaf gluing proves that every degree-zero matching family comes
from one global regular function, uniquely. -/
theorem existsUnique_zeroSection (V : X.Opens) (a : TwistedSections C 0 V) :
    ∃! s : Γ(X, V), ∀ i, res (inf_le_left : V ⊓ C.cover i ≤ V) s = a.1 i := by
  apply X.sheaf.existsUnique_gluing' (fun i => V ⊓ C.cover i) V
    (fun i => homOfLE inf_le_left) (cover_intersection C V)
  intro i j
  have ha := a.2 i j
  have ha' := congrArg (res (show (V ⊓ C.cover i) ⊓ (V ⊓ C.cover j) ≤
      overlap C V i j from le_inf inf_le_left (inf_le_right.trans inf_le_right))) ha
  simpa only [map_mul, pow_zero, map_one, one_mul, res_comp] using ha'

def zeroSectionLinear (V : X.Opens) : Γ(X, V) →ₗ[Γ(X, V)] TwistedSections C 0 V where
  toFun := zeroSection C V
  map_add' a b := by ext i; exact map_add _ _ _
  map_smul' r a := by
    ext i
    change res _ (r * a) = res _ r * res _ a
    exact map_mul _ _ _

theorem zeroSectionLinear_bijective (V : X.Opens) :
    Function.Bijective (zeroSectionLinear C V) := by
  constructor
  · intro s t h
    have hs : ∀ i, res (inf_le_left : V ⊓ C.cover i ≤ V) s = (zeroSection C V t).1 i :=
      fun i => congrArg (fun z : TwistedSections C 0 V => z.1 i) h
    have ht : ∀ i, res (inf_le_left : V ⊓ C.cover i ≤ V) t = (zeroSection C V t).1 i :=
      fun _ => rfl
    exact (existsUnique_zeroSection C V (zeroSection C V t)).unique hs ht
  · intro a
    obtain ⟨s, hs, _⟩ := existsUnique_zeroSection C V a
    refine ⟨s, ?_⟩
    ext i
    exact hs i

/-- The degree-zero piece is the full ring of regular functions as a module. -/
def degreeZeroEquiv (V : X.Opens) : Γ(X, V) ≃ₗ[Γ(X, V)] TwistedSections C 0 V :=
  LinearEquiv.ofBijective (zeroSectionLinear C V) (zeroSectionLinear_bijective C V)

end

end ArithDyn.Extension.SectionAlgebra
