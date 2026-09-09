import ArithDyn.Extension.ProjRadical

/-!
# Positive-degree homogeneous ring maps

Coordinate substitutions multiply degrees instead of preserving them. This file
constructs their maps on homogeneous prime ideals and homogeneous localizations
directly, retaining the original rings and every fraction. The degree condition
is proved at each application; no projective morphism is included in the input.
-/

set_option autoImplicit false

noncomputable section

universe u

open HomogeneousIdeal HomogeneousLocalization DirectSum

namespace ArithDyn.Extension

variable {A B C σ τ ψ : Type u} [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- A ring homomorphism which multiplies all homogeneous degrees by `d`. -/
def DegreeScaledHom (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (d : ℕ) :=
  {f : A →+* B // ∀ n x, x ∈ 𝒜 n → f x ∈ ℬ (d * n)}

namespace DegreeScaledHom

variable {d e : ℕ}

def comp (g : DegreeScaledHom ℬ 𝒞 e) (f : DegreeScaledHom 𝒜 ℬ d) :
    DegreeScaledHom 𝒜 𝒞 (e * d) :=
  ⟨g.1.comp f.1, fun n x hx => by
    simpa only [Nat.mul_assoc] using g.2 (d * n) (f.1 x) (f.2 n x hx)⟩

/-- The degree-scaling condition identifies each original homogeneous component. -/
theorem map_proj (f : DegreeScaledHom 𝒜 ℬ d) (hd : 0 < d) (n : ℕ) (x : A) :
    f.1 (GradedRing.proj 𝒜 n x) = GradedRing.proj ℬ (d * n) (f.1 x) := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i x =>
    by_cases h : i = n
    · subst i
      simp only [GradedRing.proj_apply, decompose_of_mem_same 𝒜 x.2,
        decompose_of_mem_same ℬ (f.2 n x x.2)]
    · have h' : d * i ≠ d * n := fun he => h (Nat.eq_of_mul_eq_mul_left hd he)
      simp only [GradedRing.proj_apply, decompose_of_mem_ne 𝒜 x.2 h,
        map_zero, decompose_of_mem_ne ℬ (f.2 i x x.2) h']
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Comap preserves homogeneous ideals without replacing them by radicals. -/
def idealComap (f : DegreeScaledHom 𝒜 ℬ d) (hd : 0 < d)
    (J : HomogeneousIdeal ℬ) : HomogeneousIdeal 𝒜 :=
  ⟨J.toIdeal.comap f.1, by
    intro n x hx
    change f.1 (GradedRing.proj 𝒜 n x) ∈ J.toIdeal
    rw [map_proj f hd]
    exact J.isHomogeneous (d * n) hx⟩

/-- The same numerator and denominator, mapped to their scaled degree. -/
def mapFraction (f : DegreeScaledHom 𝒜 ℬ d) {P : Submonoid A} {Q : Submonoid B}
    (h : P ≤ Q.comap f.1) (c : NumDenSameDeg 𝒜 P) : NumDenSameDeg ℬ Q :=
  ⟨d * c.deg, ⟨f.1 c.num, f.2 c.deg c.num c.num.2⟩,
    ⟨f.1 c.den, f.2 c.deg c.den c.den.2⟩, h c.den_mem⟩

/-- The actual homomorphism of zero-degree homogeneous localizations. -/
def localizationMap (f : DegreeScaledHom 𝒜 ℬ d)
    {P : Submonoid A} {Q : Submonoid B} (h : P ≤ Q.comap f.1) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q where
  toFun := Quotient.map' (mapFraction f h) (fun x y (he : x.embedding = y.embedding) => by
    apply_fun IsLocalization.map (Localization Q) f.1 h at he
    change (mapFraction f h x).embedding = (mapFraction f h y).embedding
    simp only [NumDenSameDeg.embedding, Localization.mk_eq_mk', IsLocalization.map_mk'] at he
    simpa only [mapFraction, NumDenSameDeg.embedding, Localization.mk_eq_mk'] using he)
  map_add' := Quotient.ind₂' fun x y => by
    simp only [← mk_add, Quotient.map'_mk'']
    apply val_injective
    simpa [mapFraction] using (Localization.add_mk (f.1 x.num) ⟨f.1 x.den, h x.den_mem⟩
      (f.1 y.num) ⟨f.1 y.den, h y.den_mem⟩).symm
  map_mul' := Quotient.ind₂' fun x y => by
    simp only [← mk_mul, Quotient.map'_mk'']
    apply val_injective
    simpa [mapFraction] using (Localization.mk_mul (f.1 x.num) (f.1 y.num)
      ⟨f.1 x.den, h x.den_mem⟩ ⟨f.1 y.den, h y.den_mem⟩).symm
  map_zero' := by
    simp only [← mk_zero (𝒜 := 𝒜), Quotient.map'_mk'']
    apply val_injective
    simp [mapFraction, Localization.mk_eq_mk']
  map_one' := by
    simp only [← mk_one (𝒜 := 𝒜), Quotient.map'_mk'']
    apply val_injective
    simp [mapFraction]

@[simp] theorem localizationMap_mk (f : DegreeScaledHom 𝒜 ℬ d)
    {P : Submonoid A} {Q : Submonoid B} (h : P ≤ Q.comap f.1) (c : NumDenSameDeg 𝒜 P) :
    localizationMap f h (mk c) = mk (mapFraction f h c) := rfl

@[simp] theorem val_localizationMap (f : DegreeScaledHom 𝒜 ℬ d)
    {P : Submonoid A} {Q : Submonoid B} (h : P ≤ Q.comap f.1)
    (x : HomogeneousLocalization 𝒜 P) :
    (localizationMap f h x).val = IsLocalization.map (Localization Q) f.1 h x.val := by
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp [mapFraction, Localization.mk_eq_mk', IsLocalization.map_mk']

/-- A scaled-degree map still induces a local homomorphism at a prime. -/
def localRingHom (f : DegreeScaledHom 𝒜 ℬ d)
    (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f.1) :
    AtPrime 𝒜 I →+* AtPrime ℬ J :=
  localizationMap f (Localization.le_comap_primeCompl_iff.mpr (hIJ ▸ le_rfl))

@[simp] theorem val_localRingHom (f : DegreeScaledHom 𝒜 ℬ d)
    (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f.1)
    (x : AtPrime 𝒜 I) :
    (localRingHom f I J hIJ x).val = Localization.localRingHom I J f.1 hIJ x.val :=
  val_localizationMap ..

instance (f : DegreeScaledHom 𝒜 ℬ d)
    (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f.1) :
    IsLocalHom (localRingHom f I J hIJ) where
  map_nonunit x hx := by
    rw [← isUnit_iff_isUnit_val] at hx ⊢
    rw [val_localRingHom] at hx
    exact IsLocalHom.map_nonunit _ hx

/-- Composition of scaled maps acts on the identical ambient fractions. -/
theorem localizationMap_comp (f : DegreeScaledHom 𝒜 ℬ d)
    (g : DegreeScaledHom ℬ 𝒞 e) {P : Submonoid A} {Q : Submonoid B} {R : Submonoid C}
    (hf : P ≤ Q.comap f.1) (hg : Q ≤ R.comap g.1) :
    localizationMap (comp g f) (hf.trans (Submonoid.monotone_comap hg)) =
      (localizationMap g hg).comp (localizationMap f hf) := by
  apply RingHom.ext
  intro x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  apply val_injective
  rfl

end DegreeScaledHom

end ArithDyn.Extension
