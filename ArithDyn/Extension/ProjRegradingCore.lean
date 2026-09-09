import ArithDyn.Extension.DegreeMap

/-!
# Constant positive regrading of Proj

Reindexing all polynomial degrees by multiplication with a positive integer leaves
homogeneous elements and degree-zero localizations unchanged.  The maps below retain
the same underlying polynomials and ambient fractions.  Regrading a scheme does not
identify its degree-one twists: the weighted degree `d` twist corresponds to standard
degree one; no assertion about twists is made here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

namespace ArithDyn.Extension

open MvPolynomial HomogeneousIdeal AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable {k : Type u} {ι : Type v} [Field k]

/-- Constant weights multiply the ordinary monomial weight by `d`. -/
theorem constant_weight_eq (d : ℕ) (a : ι →₀ ℕ) :
    Finsupp.weight (fun _ : ι => d) a = d * Finsupp.weight (1 : ι → ℕ) a := by
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Pi.one_apply, mul_one]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => Nat.mul_comm _ _)

/-- Standard homogeneous forms remain homogeneous after multiplying all weights. -/
theorem isWeightedHomogeneous_of_isHomogeneous (d : ℕ) {n : ℕ}
    {p : MvPolynomial ι k} (hp : p.IsHomogeneous n) :
    p.IsWeightedHomogeneous (fun _ : ι => d) (d * n) := by
  intro a ha
  rw [constant_weight_eq, hp ha]

/-- Dividing a constant positive weighted degree recovers the ordinary degree.
The statement also includes the zero polynomial. -/
theorem isHomogeneous_of_isWeightedHomogeneous (d : ℕ) (hd : 0 < d) {m : ℕ}
    {p : MvPolynomial ι k} (hp : p.IsWeightedHomogeneous (fun _ : ι => d) m) :
    p.IsHomogeneous (m / d) := by
  intro a ha
  have h := hp ha
  rw [constant_weight_eq] at h
  rw [← h, Nat.mul_div_right _ hd]

open HomogeneousLocalization

/-- Reindex a fraction of standard degree `n` as a fraction of weighted degree
`d*n`, leaving its numerator and denominator unchanged. -/
def fractionToConstantWeight (d : ℕ) (S : Submonoid (MvPolynomial ι k))
    (c : NumDenSameDeg (homogeneousSubmodule ι k) S) :
    NumDenSameDeg (constantWeightGrading ι k d) S :=
  ⟨d * c.deg, ⟨c.num, isWeightedHomogeneous_of_isHomogeneous d c.num.2⟩,
    ⟨c.den, isWeightedHomogeneous_of_isHomogeneous d c.den.2⟩, c.den_mem⟩

/-- Reindex a weighted fraction by dividing its degree.  Even when its numerator
is zero, numerator and denominator remain in the same ordinary homogeneous piece. -/
def fractionFromConstantWeight (d : ℕ) (hd : 0 < d)
    (S : Submonoid (MvPolynomial ι k))
    (c : NumDenSameDeg (constantWeightGrading ι k d) S) :
    NumDenSameDeg (homogeneousSubmodule ι k) S :=
  ⟨c.deg / d, ⟨c.num, isHomogeneous_of_isWeightedHomogeneous d hd c.num.2⟩,
    ⟨c.den, isHomogeneous_of_isWeightedHomogeneous d hd c.den.2⟩, c.den_mem⟩

/-- The forward regrading of the zero-degree homogeneous localization. -/
def localizationToConstantWeight (d : ℕ) (S : Submonoid (MvPolynomial ι k)) :
    HomogeneousLocalization (homogeneousSubmodule ι k) S →+*
      HomogeneousLocalization (constantWeightGrading ι k d) S where
  toFun := Quotient.map' (fractionToConstantWeight d S) (fun _ _ h => h)
  map_one' := by apply val_injective; rfl
  map_zero' := by apply val_injective; rfl
  map_add' x y := by
    obtain ⟨a, rfl⟩ := x.mk_surjective
    obtain ⟨b, rfl⟩ := y.mk_surjective
    apply val_injective
    simp only [← mk_add]
    rfl
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := x.mk_surjective
    obtain ⟨b, rfl⟩ := y.mk_surjective
    apply val_injective
    simp only [← mk_mul]
    rfl

@[simp] theorem val_localizationToConstantWeight (d : ℕ)
    (S : Submonoid (MvPolynomial ι k))
    (x : HomogeneousLocalization (homogeneousSubmodule ι k) S) :
    (localizationToConstantWeight d S x).val = x.val := by
  obtain ⟨a, rfl⟩ := x.mk_surjective
  rfl

/-- The inverse regrading of the zero-degree homogeneous localization. -/
def localizationFromConstantWeight (d : ℕ) (hd : 0 < d)
    (S : Submonoid (MvPolynomial ι k)) :
    HomogeneousLocalization (constantWeightGrading ι k d) S →+*
      HomogeneousLocalization (homogeneousSubmodule ι k) S where
  toFun := Quotient.map' (fractionFromConstantWeight d hd S) (fun _ _ h => h)
  map_one' := by apply val_injective; rfl
  map_zero' := by apply val_injective; rfl
  map_add' x y := by
    obtain ⟨a, rfl⟩ := x.mk_surjective
    obtain ⟨b, rfl⟩ := y.mk_surjective
    apply val_injective
    simp only [← mk_add]
    rfl
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := x.mk_surjective
    obtain ⟨b, rfl⟩ := y.mk_surjective
    apply val_injective
    simp only [← mk_mul]
    rfl

@[simp] theorem val_localizationFromConstantWeight (d : ℕ) (hd : 0 < d)
    (S : Submonoid (MvPolynomial ι k))
    (x : HomogeneousLocalization (constantWeightGrading ι k d) S) :
    (localizationFromConstantWeight d hd S x).val = x.val := by
  obtain ⟨a, rfl⟩ := x.mk_surjective
  rfl

/-- Constant positive regrading preserves every homogeneous localization as a ring,
through the identity on ambient fractions.  This includes the chart rings and stalks. -/
def localizationConstantWeightEquiv (d : ℕ) (hd : 0 < d)
    (S : Submonoid (MvPolynomial ι k)) :
    HomogeneousLocalization (homogeneousSubmodule ι k) S ≃+*
      HomogeneousLocalization (constantWeightGrading ι k d) S where
  __ := localizationToConstantWeight d S
  invFun := localizationFromConstantWeight d hd S
  left_inv x := by apply val_injective; simp
  right_inv x := by apply val_injective; simp

/-- Regrading preserves homogeneity of ideals, by preserving homogeneous generators. -/
theorem homogeneousIdeal_toConstantWeight (d : ℕ) (I : Ideal (MvPolynomial ι k))
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    I.IsHomogeneous (constantWeightGrading ι k d) := by
  obtain ⟨S, rfl⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  apply Ideal.homogeneous_span
  rintro _ ⟨⟨p, n, hp⟩, _, rfl⟩
  exact ⟨d * n, isWeightedHomogeneous_of_isHomogeneous d hp⟩

/-- The converse transfer of homogeneous ideals for a positive constant weight. -/
theorem homogeneousIdeal_fromConstantWeight (d : ℕ) (hd : 0 < d)
    (I : Ideal (MvPolynomial ι k)) (hI : I.IsHomogeneous (constantWeightGrading ι k d)) :
    I.IsHomogeneous (homogeneousSubmodule ι k) := by
  obtain ⟨S, rfl⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  apply Ideal.homogeneous_span
  rintro _ ⟨⟨p, n, hp⟩, _, rfl⟩
  exact ⟨n / d, isHomogeneous_of_isWeightedHomogeneous d hd hp⟩

/-- The irrelevant ideal is unchanged by constant positive regrading. -/
theorem constantWeight_irrelevant_eq (d : ℕ) (hd : 0 < d) :
    (irrelevant (constantWeightGrading ι k d)).toIdeal =
      (irrelevant (homogeneousSubmodule ι k)).toIdeal := by
  rw [standard_irrelevant_eq_coordinateIdeal]
  apply le_antisymm
  · apply (toIdeal_irrelevant_le _).mpr
    intro n hn p hp
    change p ∈ idealOfVars ι k
    rw [← pow_one (idealOfVars ι k), mem_pow_idealOfVars_iff]
    intro a ha
    have h := hp (mem_support_iff.mp ha)
    rw [constant_weight_eq, Pi.one_def, ← Finsupp.degree_eq_weight_one] at h
    by_contra h'
    have ha0 : a.degree = 0 := by omega
    rw [ha0, mul_zero] at h
    omega
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact mem_irrelevant_of_mem _ hd (isWeightedHomogeneous_X k (fun _ : ι => d) i)

/-- A homogeneous prime ideal regarded in the constant-weight grading. -/
def pointToConstantWeight (d : ℕ) (hd : 0 < d)
    (p : ProjectiveSpectrum (homogeneousSubmodule ι k)) :
    ProjectiveSpectrum (constantWeightGrading ι k d) where
  asHomogeneousIdeal := ⟨p.1.toIdeal, homogeneousIdeal_toConstantWeight d _ p.1.isHomogeneous⟩
  isPrime := p.isPrime
  not_irrelevant_le h := p.not_irrelevant_le <| toIdeal_le_toIdeal_iff.mp <| by
    rw [← constantWeight_irrelevant_eq d hd]
    exact h

/-- A homogeneous prime ideal regarded in the standard grading. -/
def pointFromConstantWeight (d : ℕ) (hd : 0 < d)
    (p : ProjectiveSpectrum (constantWeightGrading ι k d)) :
    ProjectiveSpectrum (homogeneousSubmodule ι k) where
  asHomogeneousIdeal := ⟨p.1.toIdeal, homogeneousIdeal_fromConstantWeight d hd _ p.1.isHomogeneous⟩
  isPrime := p.isPrime
  not_irrelevant_le h := p.not_irrelevant_le <| toIdeal_le_toIdeal_iff.mp <| by
    rw [constantWeight_irrelevant_eq d hd]
    exact h

@[simp] theorem pointFromConstantWeight_to (d : ℕ) (hd : 0 < d)
    (p : ProjectiveSpectrum (homogeneousSubmodule ι k)) :
    pointFromConstantWeight d hd (pointToConstantWeight d hd p) = p := rfl

@[simp] theorem pointToConstantWeight_from (d : ℕ) (hd : 0 < d)
    (p : ProjectiveSpectrum (constantWeightGrading ι k d)) :
    pointToConstantWeight d hd (pointFromConstantWeight d hd p) = p := rfl

open TopologicalSpace

/-- The canonical homeomorphism under a constant positive regrading. -/
def constantWeightHomeomorph (d : ℕ) (hd : 0 < d) :
    ProjectiveSpectrum (homogeneousSubmodule ι k) ≃ₜ
      ProjectiveSpectrum (constantWeightGrading ι k d) where
  toFun := pointToConstantWeight d hd
  invFun := pointFromConstantWeight d hd
  left_inv := pointFromConstantWeight_to d hd
  right_inv := pointToConstantWeight_from d hd
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, ProjectiveSpectrum.isClosed_iff_zeroLocus,
      exists_imp, forall_eq_apply_imp_iff]
    exact fun s => ⟨s, rfl⟩
  continuous_invFun := by
    simp_rw [continuous_iff_isClosed, ProjectiveSpectrum.isClosed_iff_zeroLocus,
      exists_imp, forall_eq_apply_imp_iff]
    exact fun s => ⟨s, rfl⟩

open AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf

/-- Pull a weighted section back along the regrading homeomorphism. -/
def sectionFromConstantWeightFun (d : ℕ) (hd : 0 < d)
    (U : Opens (ProjectiveSpectrum (constantWeightGrading ι k d)))
    (V : Opens (ProjectiveSpectrum (homogeneousSubmodule ι k)))
    (hUV : V.1 ⊆ (constantWeightHomeomorph d hd) ⁻¹' U.1)
    (s : ∀ x : U, AtPrime (constantWeightGrading ι k d) x.1.1.1) (y : V) :
    AtPrime (homogeneousSubmodule ι k) y.1.1.1 :=
  localizationFromConstantWeight (k := k) (ι := ι) d hd y.1.1.toIdeal.primeCompl (s ⟨pointToConstantWeight d hd y.1, hUV y.2⟩)

set_option backward.isDefEq.respectTransparency false in
theorem isLocallyFraction_sectionFromConstantWeight (d : ℕ) (hd : 0 < d)
    (U : Opens (ProjectiveSpectrum (constantWeightGrading ι k d)))
    (V : Opens (ProjectiveSpectrum (homogeneousSubmodule ι k)))
    (hUV : V.1 ⊆ (constantWeightHomeomorph d hd) ⁻¹' U.1)
    (s : ∀ x : U, AtPrime (constantWeightGrading ι k d) x.1.1.1)
    (hs : (isLocallyFraction (constantWeightGrading ι k d)).pred s) :
    (isLocallyFraction (homogeneousSubmodule ι k)).pred
      (sectionFromConstantWeightFun d hd U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨pointToConstantWeight d hd p, hUV hpV⟩ with
    ⟨W, m, iWU, n, a, b, hb, hfrac⟩
  refine ⟨W.comap ⟨constantWeightHomeomorph d hd, (constantWeightHomeomorph d hd).continuous_toFun⟩ ⊓ V,
    ⟨m, hpV⟩, Opens.infLERight _ _, n / d,
    ⟨a, isHomogeneous_of_isWeightedHomogeneous d hd a.2⟩,
    ⟨b, isHomogeneous_of_isWeightedHomogeneous d hd b.2⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ => hb ⟨_, hqW⟩, ?_⟩
  rintro ⟨q, hqW, hqV⟩
  apply val_injective
  simp only [sectionFromConstantWeightFun, val_localizationFromConstantWeight]
  exact congrArg HomogeneousLocalization.val (hfrac ⟨pointToConstantWeight d hd q, hqW⟩)

/-- The regrading map on rings of sections. -/
def sectionFromConstantWeight (d : ℕ) (hd : 0 < d)
    (U : Opens (ProjectiveSpectrum (constantWeightGrading ι k d)))
    (V : Opens (ProjectiveSpectrum (homogeneousSubmodule ι k)))
    (hUV : V.1 ⊆ (constantWeightHomeomorph d hd) ⁻¹' U.1) :
    (ProjectiveSpectrum.Proj.structureSheaf (constantWeightGrading ι k d)).1.obj (.op U) →+*
      (ProjectiveSpectrum.Proj.structureSheaf (homogeneousSubmodule ι k)).1.obj (.op V) where
  toFun s := ⟨sectionFromConstantWeightFun d hd U V hUV s.1,
    isLocallyFraction_sectionFromConstantWeight d hd U V hUV s.1 s.2⟩
  map_one' := by ext; simp [sectionFromConstantWeightFun]
  map_zero' := by ext; simp [sectionFromConstantWeightFun]
  map_add' x y := by ext; simp [sectionFromConstantWeightFun]
  map_mul' x y := by ext; simp [sectionFromConstantWeightFun]

/-- Pull a standard section back along the inverse regrading homeomorphism. -/
def sectionToConstantWeightFun (d : ℕ) (hd : 0 < d)
    (U : Opens (ProjectiveSpectrum (homogeneousSubmodule ι k)))
    (V : Opens (ProjectiveSpectrum (constantWeightGrading ι k d)))
    (hUV : V.1 ⊆ (constantWeightHomeomorph d hd).symm ⁻¹' U.1)
    (s : ∀ x : U, AtPrime (homogeneousSubmodule ι k) x.1.1.1) (y : V) :
    AtPrime (constantWeightGrading ι k d) y.1.1.1 :=
  localizationToConstantWeight (k := k) (ι := ι) d y.1.1.toIdeal.primeCompl (s ⟨pointFromConstantWeight d hd y.1, hUV y.2⟩)

set_option backward.isDefEq.respectTransparency false in
theorem isLocallyFraction_sectionToConstantWeight (d : ℕ) (hd : 0 < d)
    (U : Opens (ProjectiveSpectrum (homogeneousSubmodule ι k)))
    (V : Opens (ProjectiveSpectrum (constantWeightGrading ι k d)))
    (hUV : V.1 ⊆ (constantWeightHomeomorph d hd).symm ⁻¹' U.1)
    (s : ∀ x : U, AtPrime (homogeneousSubmodule ι k) x.1.1.1)
    (hs : (isLocallyFraction (homogeneousSubmodule ι k)).pred s) :
    (isLocallyFraction (constantWeightGrading ι k d)).pred
      (sectionToConstantWeightFun d hd U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨pointFromConstantWeight d hd p, hUV hpV⟩ with
    ⟨W, m, iWU, n, a, b, hb, hfrac⟩
  refine ⟨W.comap ⟨(constantWeightHomeomorph d hd).symm, (constantWeightHomeomorph d hd).continuous_invFun⟩ ⊓ V,
    ⟨m, hpV⟩, Opens.infLERight _ _, d * n,
    ⟨a, isWeightedHomogeneous_of_isHomogeneous d a.2⟩,
    ⟨b, isWeightedHomogeneous_of_isHomogeneous d b.2⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ => hb ⟨_, hqW⟩, ?_⟩
  rintro ⟨q, hqW, hqV⟩
  apply val_injective
  simp only [sectionToConstantWeightFun, val_localizationToConstantWeight]
  exact congrArg HomogeneousLocalization.val (hfrac ⟨pointFromConstantWeight d hd q, hqW⟩)

/-- The inverse regrading map on rings of sections. -/
def sectionToConstantWeight (d : ℕ) (hd : 0 < d)
    (U : Opens (ProjectiveSpectrum (homogeneousSubmodule ι k)))
    (V : Opens (ProjectiveSpectrum (constantWeightGrading ι k d)))
    (hUV : V.1 ⊆ (constantWeightHomeomorph d hd).symm ⁻¹' U.1) :
    (ProjectiveSpectrum.Proj.structureSheaf (homogeneousSubmodule ι k)).1.obj (.op U) →+*
      (ProjectiveSpectrum.Proj.structureSheaf (constantWeightGrading ι k d)).1.obj (.op V) where
  toFun s := ⟨sectionToConstantWeightFun d hd U V hUV s.1,
    isLocallyFraction_sectionToConstantWeight d hd U V hUV s.1 s.2⟩
  map_one' := by ext; simp [sectionToConstantWeightFun]
  map_zero' := by ext; simp [sectionToConstantWeightFun]
  map_add' x y := by ext; simp [sectionToConstantWeightFun]
  map_mul' x y := by ext; simp [sectionToConstantWeightFun]

end ArithDyn.Extension
