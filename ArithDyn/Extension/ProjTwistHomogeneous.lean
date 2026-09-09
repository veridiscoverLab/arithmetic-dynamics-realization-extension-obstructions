import ArithDyn.Extension.ProjTwistLocal
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Actual transition units from homogeneous coordinates

The fractions in this file are sections of the original Proj structure sheaf,
including all nilpotents.  Their equalities are proved inside homogeneous
localizations, not by evaluation at field-valued points.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w
open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite HomogeneousLocalization

namespace ArithDyn.Extension.ProjTwist

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A homogeneous ratio is an actual regular section wherever its denominator is invertible. -/
def homogeneousRatio {n : ℕ} (a b : A) (ha : a ∈ 𝒜 n) (hb : b ∈ 𝒜 n)
    (V : (Proj 𝒜).Opens) (hV : V ≤ Proj.basicOpen 𝒜 b) : Γ(Proj 𝒜, V) := by
  refine ⟨fun x => HomogeneousLocalization.mk ⟨n, ⟨a, ha⟩, ⟨b, hb⟩, hV x.2⟩, ?_⟩
  intro x
  exact ⟨V, x.2, 𝟙 V, n, ⟨a, ha⟩, ⟨b, hb⟩, fun y => hV y.2, fun _ => rfl⟩

@[simp] theorem res_homogeneousRatio {n : ℕ} (a b : A)
    (ha : a ∈ 𝒜 n) (hb : b ∈ 𝒜 n) {V W : (Proj 𝒜).Opens}
    (h : V ≤ W) (hW : W ≤ Proj.basicOpen 𝒜 b) :
    res h (homogeneousRatio 𝒜 a b ha hb W hW) =
      homogeneousRatio 𝒜 a b ha hb V (h.trans hW) := rfl

/-- Cancellation takes place inside each actual localization. -/
theorem homogeneousRatio_self {n : ℕ} (a : A) (ha : a ∈ 𝒜 n)
    (V : (Proj 𝒜).Opens) (hV : V ≤ Proj.basicOpen 𝒜 a) :
    homogeneousRatio 𝒜 a a ha ha V hV = 1 := by
  apply Subtype.ext
  funext x
  change HomogeneousLocalization.mk _ = (1 : HomogeneousLocalization.AtPrime 𝒜
    x.1.asHomogeneousIdeal.toIdeal)
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
  change (Localization.mk a ⟨a, hV x.2⟩ :
    Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) = 1
  exact Localization.mk_self (⟨a, hV x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)

/-- The common middle coordinate cancels, with no reduction of the scheme. -/
theorem homogeneousRatio_comp {n : ℕ} (a b c : A)
    (ha : a ∈ 𝒜 n) (hb : b ∈ 𝒜 n) (hc : c ∈ 𝒜 n)
    (V : (Proj 𝒜).Opens) (hVa : V ≤ Proj.basicOpen 𝒜 a)
    (hVb : V ≤ Proj.basicOpen 𝒜 b) :
    homogeneousRatio 𝒜 b a hb ha V hVa * homogeneousRatio 𝒜 c b hc hb V hVb =
      homogeneousRatio 𝒜 c a hc ha V hVa := by
  apply Subtype.ext
  funext x
  change HomogeneousLocalization.mk _ * HomogeneousLocalization.mk _ =
    (HomogeneousLocalization.mk _ : HomogeneousLocalization.AtPrime 𝒜
      x.1.asHomogeneousIdeal.toIdeal)
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  change (Localization.mk b ⟨a, hVa x.2⟩ :
    Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) * Localization.mk c ⟨b, hVb x.2⟩ =
    Localization.mk c ⟨a, hVa x.2⟩
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- Equal-degree coordinates give actual unit transition functions on each overlap. -/
def homogeneousRatioUnit {n : ℕ} (a b : A) (ha : a ∈ 𝒜 n) (hb : b ∈ 𝒜 n)
    (V : (Proj 𝒜).Opens) (hVa : V ≤ Proj.basicOpen 𝒜 a)
    (hVb : V ≤ Proj.basicOpen 𝒜 b) : Γ(Proj 𝒜, V)ˣ where
  val := homogeneousRatio 𝒜 b a hb ha V hVa
  inv := homogeneousRatio 𝒜 a b ha hb V hVb
  val_inv := by rw [homogeneousRatio_comp, homogeneousRatio_self]
  inv_val := by rw [homogeneousRatio_comp, homogeneousRatio_self]

/-- A single homogeneous coordinate cover supplies the complete unit cocycle. -/
def homogeneousCocycle {ι : Type w} {n : ℕ} (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 n)
    (hcover : iSup (fun i => Proj.basicOpen 𝒜 (f i)) = ⊤) : UnitCocycle (Proj 𝒜) ι where
  cover i := Proj.basicOpen 𝒜 (f i)
  covers := hcover
  g i j V hi hj := homogeneousRatioUnit 𝒜 (f i) (f j) (hf i) (hf j) V hi hj
  naturality i j V W h hi hj := by apply Units.ext; rfl
  self i V hi := by apply Units.ext; exact homogeneousRatio_self 𝒜 (f i) (hf i) V hi
  comp i j k V hi hj hk := by
    apply Units.ext
    exact homogeneousRatio_comp 𝒜 _ _ _ (hf i) (hf j) (hf k) V hi hj

end ArithDyn.Extension.ProjTwist
