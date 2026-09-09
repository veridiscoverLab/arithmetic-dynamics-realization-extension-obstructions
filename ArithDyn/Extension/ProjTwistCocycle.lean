import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Complete matching families for unit transition cocycles

Every degree uses the same cover and the same unit cocycle.  Sections retain all
overlap equations simultaneously.  No line-bundle isomorphism is an input.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{u}}

/-- Restriction in the original structure sheaf. -/
def res {U V : X.Opens} (h : U ≤ V) : Γ(X, V) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE h).op).hom

@[simp] theorem res_refl (U : X.Opens) (a : Γ(X, U)) :
    res (le_refl U) a = a := by
  simp [res]

@[simp] theorem res_comp {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W)
    (a : Γ(X, W)) : res hUV (res hVW a) = res (hUV.trans hVW) a := by
  change ((X.presheaf.map (homOfLE hVW).op) ≫
    X.presheaf.map (homOfLE hUV).op) a = _
  rw [← X.presheaf.map_comp]
  rfl

/-- A unit cocycle, including its restrictions to every common open subset.
The condition is an actual equality of regular sections, not a pointwise test. -/
structure UnitCocycle (X : Scheme.{u}) (ι : Type v) where
  cover : ι → X.Opens
  covers : iSup cover = ⊤
  g : (i j : ι) → (V : X.Opens) → V ≤ cover i → V ≤ cover j → Γ(X, V)ˣ
  naturality : ∀ (i j : ι) (V W : X.Opens) (h : V ≤ W)
      (hi : W ≤ cover i) (hj : W ≤ cover j),
    Units.map (res h).toMonoidHom (g i j W hi hj) =
      g i j V (h.trans hi) (h.trans hj)
  self : ∀ (i : ι) (V : X.Opens) (hi : V ≤ cover i), g i i V hi hi = 1
  comp : ∀ (i j k : ι) (V : X.Opens)
      (hi : V ≤ cover i) (hj : V ≤ cover j) (hk : V ≤ cover k),
    g i j V hi hj * g j k V hj hk = g i k V hi hk

variable {ι : Type v} (C : UnitCocycle X ι)

/-- The common overlap used by both restrictions in a matching equation. -/
abbrev overlap (V : X.Opens) (i j : ι) : X.Opens := V ⊓ C.cover i ⊓ C.cover j

/-- The scalar action on a restricted chart uses the actual restriction homomorphism. -/
instance sectionPieceModule (V U : X.Opens) :
    Module Γ(X, V) Γ(X, V ⊓ U) :=
  Module.compHom _ (res (inf_le_left : V ⊓ U ≤ V))

/-- Full compatibility of a family in a fixed nonnegative twist degree. -/
def Compatible (n : ℕ) (V : X.Opens) (a : (i : ι) → Γ(X, V ⊓ C.cover i)) : Prop :=
  ∀ i j,
    res (inf_le_left : overlap C V i j ≤ V ⊓ C.cover i) (a i) =
      (C.g i j (overlap C V i j) (inf_le_left.trans inf_le_right) inf_le_right :
        Γ(X, overlap C V i j)) ^ n *
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        overlap C V i j ≤ V ⊓ C.cover j) (a j)

lemma res_sectionPiece_smul {V U W : X.Opens} (h : W ≤ V ⊓ U)
    (r : Γ(X, V)) (a : Γ(X, V ⊓ U)) :
    res h (r • a) = res (h.trans inf_le_left) r * res h a := by
  change res h (res inf_le_left r * a) = _
  rw [map_mul, res_comp]

/-- All overlap equations form an actual submodule of the full chart-section product. -/
def sectionSubmodule (n : ℕ) (V : X.Opens) :
    Submodule Γ(X, V) ((i : ι) → Γ(X, V ⊓ C.cover i)) where
  carrier := Compatible C n V
  zero_mem' := by intro i j; simp
  add_mem' := by
    intro a b ha hb i j
    change res _ (a i + b i) = _ * res _ (a j + b j)
    rw [map_add, map_add, ha i j, hb i j, mul_add]
  smul_mem' := by
    intro r a ha i j
    change res _ (r • a i) = _ * res _ (r • a j)
    rw [res_sectionPiece_smul, res_sectionPiece_smul, ha i j]
    ring

/-- Genuine matching families; this is a subtype of all chart sections. -/
abbrev TwistedSections (n : ℕ) (V : X.Opens) := sectionSubmodule C n V

@[ext] theorem TwistedSections.ext {n : ℕ} {V : X.Opens}
    {a b : TwistedSections C n V} (h : ∀ i, a.1 i = b.1 i) : a = b :=
  Subtype.ext (funext h)

end ArithDyn.Extension.ProjTwist
