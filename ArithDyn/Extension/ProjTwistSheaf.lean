import ArithDyn.Extension.ProjTwistCocycle
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The actual presheaf and sheaf of twisted matching families

Restrictions act on every retained chart coefficient.  The sheaf condition is
proved by gluing each coefficient in the original structure sheaf and checking
all cocycle equations on a common cover.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

namespace ArithDyn.Extension.ProjTwist

variable {X : Scheme.{u}} {ι : Type v} (C : UnitCocycle X ι)

@[simp] theorem res_g (i j : ι) {V W : X.Opens} (h : V ≤ W)
    (hi : W ≤ C.cover i) (hj : W ≤ C.cover j) :
    res h (C.g i j W hi hj : Γ(X, W)) =
      (C.g i j V (h.trans hi) (h.trans hj) : Γ(X, V)) :=
  congrArg Units.val (C.naturality i j V W h hi hj)

/-- Restrict every chart coefficient, preserving the complete overlap system. -/
def restrictSections (n : ℕ) {V W : X.Opens} (h : V ≤ W)
    (a : TwistedSections C n W) : TwistedSections C n V := by
  refine ⟨fun i => res (inf_le_inf h le_rfl) (a.1 i), ?_⟩
  intro i j
  have he := congrArg (res (inf_le_inf (inf_le_inf h le_rfl) le_rfl)) (a.2 i j)
  simpa only [map_mul, map_pow, res_comp, res_g] using he

@[simp] theorem restrictSections_apply (n : ℕ) {V W : X.Opens} (h : V ≤ W)
    (a : TwistedSections C n W) (i : ι) :
    (restrictSections C n h a).1 i = res (inf_le_inf h le_rfl) (a.1 i) := rfl

@[simp] theorem restrictSections_refl (n : ℕ) (V : X.Opens)
    (a : TwistedSections C n V) : restrictSections C n le_rfl a = a := by
  ext i
  exact res_refl _ _

@[simp] theorem restrictSections_comp (n : ℕ) {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W) (a : TwistedSections C n W) :
    restrictSections C n hUV (restrictSections C n hVW a) =
      restrictSections C n (hUV.trans hVW) a := by
  ext i
  exact res_comp _ _ _

/-- The actual presheaf of modules; its sections are exactly matching families. -/
def presheaf (n : ℕ) : PresheafOfModules.{max u v} X.ringCatSheaf.obj where
  obj V := ModuleCat.of Γ(X, V.unop) (TwistedSections C n V.unop)
  map {V W} f := by
    refine ModuleCat.homMk (AddCommGrpCat.ofHom {
    toFun := restrictSections C n f.unop.le
    map_zero' := by
      apply Subtype.ext
      funext i
      exact map_zero _
    map_add' a b := by
      apply Subtype.ext
      funext i
      exact map_add _ _ _ }) ?_
    intro r
    ext a
    apply Subtype.ext
    funext i
    symm
    change res _ (res inf_le_left r * a.1 i) =
      res inf_le_left (res f.unop.le r) * res _ (a.1 i)
    rw [map_mul, res_comp, res_comp]
  map_id V := by
    ext a
    apply Subtype.ext
    funext i
    exact res_refl _ _
  map_comp f g := by
    ext a
    apply Subtype.ext
    funext i
    exact (res_comp _ _ _).symm

@[simp] theorem presheaf_map_apply (n : ℕ) {V W : X.Opens}
    (h : V ≤ W) (a : TwistedSections C n W) :
    (presheaf C n).map (homOfLE h).op a = restrictSections C n h a := rfl

/-- The overlap equation on any smaller open, without losing any chart label. -/
theorem compatible_on {n : ℕ} {V : X.Opens} (a : TwistedSections C n V)
    (i j : ι) (W : X.Opens) (hV : W ≤ V)
    (hi : W ≤ C.cover i) (hj : W ≤ C.cover j) :
    res (le_inf hV hi) (a.1 i) =
      (C.g i j W hi hj : Γ(X, W)) ^ n * res (le_inf hV hj) (a.1 j) := by
  have h := congrArg (res (le_inf (le_inf hV hi) hj)) (a.2 i j)
  simpa only [map_mul, map_pow, res_comp, res_g] using h

/-- Actual gluing in the original structure sheaf, for every coefficient at once. -/
theorem existsUnique_gluingSections {κ : Type u} (n : ℕ)
    (U : κ → X.Opens) (V : X.Opens) (hUV : ∀ a, U a ≤ V)
    (hcover : V ≤ iSup U) (s : ∀ a, TwistedSections C n (U a))
    (hs : ∀ a b, restrictSections C n inf_le_left (s a) =
      restrictSections C n (inf_le_right : U a ⊓ U b ≤ U b) (s b)) :
    ∃! t : TwistedSections C n V, ∀ a, restrictSections C n (hUV a) t = s a := by
  have hc (i : ι) : V ⊓ C.cover i ≤ ⨆ a, U a ⊓ C.cover i := by
    rw [← iSup_inf_eq]
    exact inf_le_inf hcover le_rfl
  have hg (i : ι) : ∃! t : Γ(X, V ⊓ C.cover i),
      ∀ a, res (inf_le_inf (hUV a) le_rfl) t = (s a).1 i := by
    apply X.sheaf.existsUnique_gluing' (fun a => U a ⊓ C.cover i)
      (V ⊓ C.cover i) (fun a => homOfLE (inf_le_inf (hUV a) le_rfl)) (hc i)
    intro a b
    have he := congrArg (fun t : TwistedSections C n (U a ⊓ U b) => t.1 i) (hs a b)
    have he' := congrArg (res (show (U a ⊓ C.cover i) ⊓ (U b ⊓ C.cover i) ≤
        (U a ⊓ U b) ⊓ C.cover i from
      le_inf (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left)) (inf_le_left.trans inf_le_right))) he
    simpa only [restrictSections_apply, res_comp] using he'
  choose t ht huniq using hg
  have htc : Compatible C n V t := by
    intro i j
    apply X.sheaf.eq_of_locally_eq' (fun a => U a ⊓ C.cover i ⊓ C.cover j)
      (overlap C V i j)
      (fun a => homOfLE (inf_le_inf (inf_le_inf (hUV a) le_rfl) le_rfl))
    · dsimp [overlap]
      rw [← iSup_inf_eq, ← iSup_inf_eq]
      exact inf_le_inf (inf_le_inf hcover le_rfl) le_rfl
    · intro a
      change res _ (res _ (t i)) = res _ (_ ^ n * res _ (t j))
      simp only [res_comp, map_mul, map_pow, res_g]
      have hi := congrArg (res (inf_le_left : U a ⊓ C.cover i ⊓ C.cover j ≤
          U a ⊓ C.cover i)) (ht i a)
      have hj := congrArg (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          U a ⊓ C.cover i ⊓ C.cover j ≤ U a ⊓ C.cover j)) (ht j a)
      simp only [res_comp] at hi hj
      rw [hi, hj]
      exact (s a).2 i j
  refine ⟨⟨t, htc⟩, ?_, ?_⟩
  · intro a
    ext i
    exact ht i a
  · intro t' ht'
    ext i
    apply huniq i
    intro a
    exact congrArg (fun z : TwistedSections C n (U a) => z.1 i) (ht' a)

/-- No sheafification is used: the matching-family presheaf already is a sheaf. -/
theorem presheaf_isSheaf (n : ℕ) :
    TopCat.Presheaf.IsSheaf (presheaf C n).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro κ U s hs
  exact existsUnique_gluingSections C n U (iSup U) (fun a => le_iSup U a) le_rfl s hs

/-- The actual sheaf of modules defined by the original unit cocycle. -/
def twistedModule (n : ℕ) : SheafOfModules.{max u v} X.ringCatSheaf where
  val := presheaf C n
  isSheaf := presheaf_isSheaf C n

end ArithDyn.Extension.ProjTwist
