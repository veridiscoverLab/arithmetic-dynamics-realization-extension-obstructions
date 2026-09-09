import ArithDyn.Extension.ProjCoordinateBasis
import ArithDyn.Extension.ScaledCoordinateMaps
import ArithDyn.Extension.SectionAlgebraPullback

/-!
# The complete transition system of a homogeneous polynomial map

The actual structure-sheaf map pulls `Xⱼ / Xᵢ` back to `Fⱼ / Fᵢ`.
The same fractions are the changes of basis of standard `O(d)` in its original
polynomial bases `Fᵢ`.  Every statement is on all common subopens.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

open MvPolynomial HomogeneousIdeal HomogeneousLocalization
open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace ArithDyn.Extension.ProjTwist

section Bases

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra
variable {k : Type u} {σ : Type v} [Field k]

/-- Changing the polynomial basis retains every coordinate coefficient. -/
theorem homogeneousBasisSection_change_basis (d : ℕ)
    (F G : MvPolynomial σ k) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (V : (Proj (homogeneousSubmodule σ k)).Opens)
    (hVF : V ≤ Proj.basicOpen (homogeneousSubmodule σ k) F)
    (hVG : V ≤ Proj.basicOpen (homogeneousSubmodule σ k) G) :
    homogeneousBasisSection d G hG V hVG =
      homogeneousRatio (homogeneousSubmodule σ k) G F hG hF V hVF •
        homogeneousBasisSection d F hF V hVF := by
  ext i
  change homogeneousRatio (homogeneousSubmodule σ k) G (X i ^ d) hG
      (coordinate_pow_homogeneous i d) (V ⊓ (standardCocycle k σ).cover i)
      (inf_le_right.trans (basicOpen_le_pow (homogeneousSubmodule σ k) (X i) d)) =
    res inf_le_left (homogeneousRatio (homogeneousSubmodule σ k) G F hG hF V hVF) *
      homogeneousRatio (homogeneousSubmodule σ k) F (X i ^ d) hF
        (coordinate_pow_homogeneous i d) (V ⊓ (standardCocycle k σ).cover i)
        (inf_le_right.trans (basicOpen_le_pow (homogeneousSubmodule σ k) (X i) d))
  rw [res_homogeneousRatio, mul_comm]
  exact (homogeneousRatio_comp (homogeneousSubmodule σ k) (X i ^ d) F G
    (coordinate_pow_homogeneous i d) hF hG (V ⊓ (standardCocycle k σ).cover i)
    (inf_le_right.trans (basicOpen_le_pow (homogeneousSubmodule σ k) (X i) d))
    (inf_le_left.trans hVF)).symm

/-- The actual transition matrix of the two polynomial bases is `G / F`. -/
theorem homogeneousBasisLinearEquiv_transition (d : ℕ)
    (F G : MvPolynomial σ k) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (V : (Proj (homogeneousSubmodule σ k)).Opens)
    (hVF : V ≤ Proj.basicOpen (homogeneousSubmodule σ k) F)
    (hVG : V ≤ Proj.basicOpen (homogeneousSubmodule σ k) G)
    (r : Γ(Proj (homogeneousSubmodule σ k), V)) :
    homogeneousBasisLinearEquiv d F hF V hVF
        ((homogeneousBasisLinearEquiv d G hG V hVG).symm r) =
      homogeneousRatio (homogeneousSubmodule σ k) G F hG hF V hVF * r := by
  rw [homogeneousBasisLinearEquiv_symm_apply,
    homogeneousBasisSection_change_basis d F G hF hG V hVF hVG,
    map_smul, map_smul, homogeneousBasisLinearEquiv_basis]
  change r * (homogeneousRatio (homogeneousSubmodule σ k) G F hG hF V hVF * 1) = _
  rw [mul_one, mul_comm]

end Bases

section ScaledRatios

variable {A B S T : Type w} [CommRing A] [CommRing B]
  [SetLike S A] [AddSubgroupClass S A] [SetLike T B] [AddSubgroupClass T B]
  {𝒜 : ℕ → S} {ℬ : ℕ → T} [GradedRing 𝒜] [GradedRing ℬ]

/-- The actual Proj structure-sheaf map sends a homogeneous ratio to its image ratio. -/
theorem pullRegular_projMap_homogeneousRatio {d n : ℕ}
    (f : DegreeScaledHom 𝒜 ℬ d) (hd : 0 < d)
    (hf : (irrelevant ℬ).toIdeal ≤ ((irrelevant 𝒜).toIdeal.map f.1).radical)
    (a b : A) (ha : a ∈ 𝒜 n) (hb : b ∈ 𝒜 n)
    (U : (Proj 𝒜).Opens) (V : (Proj ℬ).Opens)
    (hU : U ≤ Proj.basicOpen 𝒜 b) (hV : V ≤ DegreeScaledHom.projMap f hd hf ⁻¹ᵁ U) :
    pullRegular (DegreeScaledHom.projMap f hd hf) hV
        (homogeneousRatio 𝒜 a b ha hb U hU) =
      homogeneousRatio ℬ (f.1 a) (f.1 b) (f.2 n a ha) (f.2 n b hb) V
        (hV.trans (((Opens.map (DegreeScaledHom.projMap f hd hf).base).map
          (homOfLE hU)).le)) := by
  apply Subtype.ext
  funext p
  apply HomogeneousLocalization.val_injective
  change (DegreeScaledHom.localRingHom (𝒜 := 𝒜) (ℬ := ℬ) f
    (DegreeScaledHom.pointMap f hd hf p.1).1.toIdeal p.1.1.toIdeal rfl
    (HomogeneousLocalization.mk ⟨n, ⟨a, ha⟩, ⟨b, hb⟩, hU (hV p.2)⟩)).val = _
  rfl

end ScaledRatios

section PolynomialMap

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra
variable {k : Type u} {σ ι : Type v} [Field k] [Finite σ]
  (d : ℕ) (hd : 0 < d) (F : ι → MvPolynomial σ k)
  (hF : ∀ i, (F i).IsHomogeneous d)
  (hbase : ∀ v : σ → AlgebraicClosure k, v ≠ 0 → ∃ i, aeval v (F i) ≠ 0)

/-- The cocycle pulled back by the original actual polynomial Proj map. -/
def polynomialPullbackCocycle : UnitCocycle (Proj (homogeneousSubmodule σ k)) ι :=
  pullbackCocycle (scaledPolynomialProjMap d hd F hF hbase) (standardCocycle k ι)

@[simp] theorem polynomialPullbackCocycle_cover (i : ι) :
    (polynomialPullbackCocycle d hd F hF hbase).cover i =
      Proj.basicOpen (homogeneousSubmodule σ k) (F i) := by
  change scaledPolynomialProjMap d hd F hF hbase ⁻¹ᵁ
      ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) (X i) =
    ProjectiveSpectrum.basicOpen (homogeneousSubmodule σ k) (F i)
  rw [scaledPolynomialProjMap_preimage_basicOpen, aeval_X]

theorem polynomialBasisOpen_le (i : ι) :
    (polynomialPullbackCocycle d hd F hF hbase).cover i ≤
      Proj.basicOpen (homogeneousSubmodule σ k) (F i) :=
  (polynomialPullbackCocycle_cover d hd F hF hbase i).le

/-- Every transition is the actual original fraction `Fⱼ / Fᵢ`. -/
theorem polynomialPullbackCocycle_g_val (i j : ι)
    (V : (Proj (homogeneousSubmodule σ k)).Opens)
    (hi : V ≤ (polynomialPullbackCocycle d hd F hF hbase).cover i)
    (hj : V ≤ (polynomialPullbackCocycle d hd F hF hbase).cover j) :
    ((polynomialPullbackCocycle d hd F hF hbase).g i j V hi hj :
        Γ(Proj (homogeneousSubmodule σ k), V)) =
      homogeneousRatio (homogeneousSubmodule σ k) (F j) (F i) (hF j) (hF i) V
        (hi.trans (polynomialBasisOpen_le d hd F hF hbase i)) := by
  change pullRegular (scaledPolynomialProjMap d hd F hF hbase) (le_inf hi hj)
      ((standardCocycle k ι).g i j
        ((standardCocycle k ι).cover i ⊓ (standardCocycle k ι).cover j)
        inf_le_left inf_le_right :
          Γ(Proj (homogeneousSubmodule ι k),
            (standardCocycle k ι).cover i ⊓ (standardCocycle k ι).cover j)) = _
  rw [standardCocycle_g_val]
  simpa only [aevalDegreeScaledHom_apply, aeval_X, mul_one] using
    pullRegular_projMap_homogeneousRatio
      (𝒜 := homogeneousSubmodule ι k) (ℬ := homogeneousSubmodule σ k)
      (aevalDegreeScaledHom d F hF) hd
      (aevalDegreeScaledHom_irrelevant_of_no_basepoint d hd F hF hbase)
      (X j) (X i) (isHomogeneous_X k j) (isHomogeneous_X k i)
      ((standardCocycle k ι).cover i ⊓ (standardCocycle k ι).cover j) V
      inf_le_left (le_inf hi hj)

include d hd hF hbase in
/-- Original base-point freeness gives the cover on which these bases are used. -/
theorem polynomialCoordinateCover_covers :
    (⨆ i, Proj.basicOpen (homogeneousSubmodule σ k) (F i)) = ⊤ := by
  exact (iSup_congr fun i => polynomialPullbackCocycle_cover d hd F hF hbase i).symm.trans
    (polynomialPullbackCocycle d hd F hF hbase).covers

/-- The actual `O(d)` bases, indexed by the exact pulled-back coordinate cover. -/
def polynomialPullbackBasis (i : ι) :
    Scheme.Modules.restrict (standardO k σ d)
        ((polynomialPullbackCocycle d hd F hF hbase).cover i).ι ≅
      unitStructureModule ((polynomialPullbackCocycle d hd F hF hbase).cover i).toScheme :=
  homogeneousBasisRestrictionIso d (F i) (hF i)
    ((polynomialPullbackCocycle d hd F hF hbase).cover i)
    (polynomialBasisOpen_le d hd F hF hbase i)

/-- The same complete transition law, already indexed by the pullback cocycle. -/
theorem polynomialPullbackBasis_transition (i j : ι)
    (V : (Proj (homogeneousSubmodule σ k)).Opens)
    (hi : V ≤ (polynomialPullbackCocycle d hd F hF hbase).cover i)
    (hj : V ≤ (polynomialPullbackCocycle d hd F hF hbase).cover j)
    (r : Γ(Proj (homogeneousSubmodule σ k), V)) :
    homogeneousBasisLinearEquiv d (F i) (hF i) V
        (hi.trans (polynomialBasisOpen_le d hd F hF hbase i))
        ((homogeneousBasisLinearEquiv d (F j) (hF j) V
          (hj.trans (polynomialBasisOpen_le d hd F hF hbase j))).symm r) =
      ((polynomialPullbackCocycle d hd F hF hbase).g i j V hi hj :
        Γ(Proj (homogeneousSubmodule σ k), V)) * r := by
  rw [polynomialPullbackCocycle_g_val]
  exact homogeneousBasisLinearEquiv_transition d (F i) (F j) (hF i) (hF j) V
    (hi.trans (polynomialBasisOpen_le d hd F hF hbase i))
    (hj.trans (polynomialBasisOpen_le d hd F hF hbase j)) r

end PolynomialMap

end ArithDyn.Extension.ProjTwist
