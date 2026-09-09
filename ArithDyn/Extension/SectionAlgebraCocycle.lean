import ArithDyn.Extension.ProjTwistCocycle
import ArithDyn.Extension.SectionAlgebraDirectSum

/-!
# The section algebra of one unit cocycle on the original scheme

All degrees use the same open cover and the same transition units.  The
multiplication is the actual product of matching chart sections, and all
overlap equations are verified.  The resulting direct sum has a constructed
internal grading.  Its coefficient ring is the full `Γ(X, ⊤)`; it is never
identified with a ground field.
-/

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace DirectSum
open ArithDyn.Extension.ProjTwist

namespace ArithDyn.Extension.SectionAlgebra

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {X : Scheme.{u}} {ι : Type v} (C : UnitCocycle X ι)

/-- The scalar algebra on all chart sections uses the actual restriction maps. -/
instance sectionProductAlgebra (V : X.Opens) :
    Algebra Γ(X, V) ((i : ι) → Γ(X, V ⊓ C.cover i)) where
  algebraMap := Pi.ringHom fun i => res (inf_le_left : V ⊓ C.cover i ≤ V)
  commutes' _ _ := funext fun _ => mul_comm _ _
  smul_def' _ _ := rfl

/-- Multiplication of compatible sections retains every overlap equation. -/
theorem compatible_mul {n m : ℕ} {V : X.Opens}
    {a b : (i : ι) → Γ(X, V ⊓ C.cover i)}
    (ha : Compatible C n V a) (hb : Compatible C m V b) :
    Compatible C (n + m) V (a * b) := by
  intro i j
  change res _ (a i * b i) = _ * res _ (a j * b j)
  rw [map_mul, map_mul, ha i j, hb i j, pow_add]
  ring

theorem compatible_one (V : X.Opens) : Compatible C 0 V 1 := by
  intro i j
  simp

/-- The actual bilinear multiplication between any two twist degrees. -/
def mulSections {n m : ℕ} {V : X.Opens}
    (a : TwistedSections C n V) (b : TwistedSections C m V) :
    TwistedSections C (n + m) V :=
  ⟨a.1 * b.1, compatible_mul C a.2 b.2⟩

@[simp] theorem mulSections_apply {n m : ℕ} {V : X.Opens}
    (a : TwistedSections C n V) (b : TwistedSections C m V) (i : ι) :
    (mulSections C a b).1 i = a.1 i * b.1 i := rfl

instance sectionSubmodule_gradedMonoid (V : X.Opens) :
    SetLike.GradedMonoid (fun n => sectionSubmodule C n V) where
  one_mem := compatible_one C V
  mul_mem := by
    intro n m a b ha hb
    exact compatible_mul C ha hb

/-- The actual algebra of all nonnegative twist sections over one open subset. -/
abbrev sectionAlgebraOn (V : X.Opens) := ⨁ n : ℕ, TwistedSections C n V

/-- The full section algebra on the original scheme. -/
abbrev sectionAlgebra := sectionAlgebraOn C ⊤

/-- The homogeneous submodules are constructed inside the actual section algebra. -/
def sectionGradingOn (V : X.Opens) : ℕ → Submodule Γ(X, V) (sectionAlgebraOn C V) :=
  directSumComponent (R := Γ(X, V)) (fun n => TwistedSections C n V)

instance sectionAlgebra_graded (V : X.Opens) : GradedAlgebra (sectionGradingOn C V) :=
  directSumGradedAlgebra (R := Γ(X, V)) (fun n => TwistedSections C n V)

/-- Insertion of an actual section into its homogeneous degree. -/
def sectionInclusion (V : X.Opens) (n : ℕ) :
    TwistedSections C n V →ₗ[Γ(X, V)] sectionAlgebraOn C V :=
  DirectSum.lof Γ(X, V) ℕ (fun m => ↥(TwistedSections C m V)) n

theorem sectionInclusion_mem (V : X.Opens) (n : ℕ) (a : TwistedSections C n V) :
    sectionInclusion C V n a ∈ sectionGradingOn C V n :=
  lof_mem_directSumComponent (R := Γ(X, V)) (fun m => ↥(TwistedSections C m V)) n a

/-- The ring multiplication is exactly the product of the original chart sections. -/
theorem sectionInclusion_mul (V : X.Opens) (n m : ℕ)
    (a : TwistedSections C n V) (b : TwistedSections C m V) :
    sectionInclusion C V n a * sectionInclusion C V m b =
      sectionInclusion C V (n + m) (mulSections C a b) := by
  change DirectSum.of (fun m => ↥(TwistedSections C m V)) n a *
    DirectSum.of (fun m => ↥(TwistedSections C m V)) m b = _
  rw [DirectSum.of_mul_of]
  rfl

end

end ArithDyn.Extension.SectionAlgebra
