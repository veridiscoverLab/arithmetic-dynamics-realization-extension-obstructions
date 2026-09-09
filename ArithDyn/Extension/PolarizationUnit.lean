import ArithDyn.Extension.ProjTwistCocycle

/-!
# Units extracted from actual automorphisms of the structure module

This file proves the rank-one scalar description of actual sheaf morphisms.
It is the local input needed to take tensor powers of one fixed polarization:
the unit coefficient is extracted from the isomorphism, not supplied as data.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme

namespace ArithDyn.Extension.ProjTwist

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable (X : Scheme.{u})

/-- The actual rank-one free structure module. -/
def unitModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- A regular global function determines a compatible section family of the unit module. -/
def unitSection (s : Γ(X, ⊤)) : (unitModule X).sections :=
  PresheafOfModules.sectionsMk (fun U => res (show U.unop ≤ ⊤ from le_top) s) (by
    intro U V i
    change res (leOfHom i.unop) (res le_top s) = res le_top s
    exact res_comp _ _ s)

/-- Multiplication by a global function as an actual morphism of sheaves. -/
def unitMul (s : Γ(X, ⊤)) : unitModule X ⟶ unitModule X :=
  (SheafOfModules.unitHomEquiv (unitModule X)).symm (unitSection X s)

@[simp] theorem unitMul_app (s : Γ(X, ⊤)) (U : X.Opens) (a : Γ(X, U)) :
    (unitMul X s).app U a = a * res le_top s := rfl

/-- The coefficient of an actual rank-one sheaf endomorphism. -/
def unitCoeff (α : unitModule X ⟶ unitModule X) : Γ(X, ⊤) :=
  α.app ⊤ (1 : Γ(X, ⊤))

theorem unitHom_app_one (α : unitModule X ⟶ unitModule X) (U : X.Opens) :
    α.app U (1 : Γ(X, U)) = res le_top (unitCoeff X α) := by
  have h := α.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
  have h1 := congrArg (fun q => q (1 : Γ(X, ⊤))) h
  change α.app U (res (show U ≤ ⊤ from le_top) (1 : Γ(X, ⊤))) =
    res le_top (unitCoeff X α) at h1
  simpa only [map_one] using h1

/-- Every actual rank-one sheaf endomorphism acts by its extracted coefficient. -/
theorem unitHom_app (α : unitModule X ⟶ unitModule X) (U : X.Opens) (a : Γ(X, U)) :
    α.app U a = a * res le_top (unitCoeff X α) := by
  have h := α.app_smul (U := U) a (1 : Γ(X, U))
  let b : Γ(X, U) := α.app U (1 : Γ(X, U))
  have hb : b = res le_top (unitCoeff X α) := unitHom_app_one X α U
  change (α.app U ((a * (1 : Γ(X, U))) : Γ(X, U)) : Γ(X, U)) =
    a * b at h
  rw [hb, mul_one] at h
  exact h

theorem unitHom_eq_unitMul (α : unitModule X ⟶ unitModule X) :
    α = unitMul X (unitCoeff X α) := by
  apply Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro a
  exact unitHom_app X α U a

@[simp] theorem unitCoeff_unitMul (s : Γ(X, ⊤)) :
    unitCoeff X (unitMul X s) = s := by
  simp [unitCoeff]

@[simp] theorem unitCoeff_id : unitCoeff X (𝟙 (unitModule X)) = 1 := rfl

theorem unitCoeff_comp (α β : unitModule X ⟶ unitModule X) :
    unitCoeff X (α ≫ β) = unitCoeff X α * unitCoeff X β := by
  change β.app ⊤ (unitCoeff X α) = _
  simpa using unitHom_app X β ⊤ (unitCoeff X α)

@[simp] theorem unitMul_one : unitMul X 1 = 𝟙 (unitModule X) := by
  simpa using (unitHom_eq_unitMul X (𝟙 (unitModule X))).symm

theorem unitMul_comp (s t : Γ(X, ⊤)) :
    unitMul X s ≫ unitMul X t = unitMul X (s * t) := by
  rw [unitHom_eq_unitMul X (unitMul X s ≫ unitMul X t), unitCoeff_comp]
  simp

/-- A global unit gives an actual automorphism of the structure module. -/
def unitIsoOfUnit (s : Γ(X, ⊤)ˣ) : Aut (unitModule X) where
  hom := unitMul X s
  inv := unitMul X (↑s⁻¹ : Γ(X, ⊤))
  hom_inv_id := by rw [unitMul_comp]; simp
  inv_hom_id := by rw [unitMul_comp]; simp

/-- The coefficient of an actual sheaf isomorphism is proved to be a unit. -/
def unitOfIso (e : unitModule X ≅ unitModule X) : Γ(X, ⊤)ˣ where
  val := unitCoeff X e.hom
  inv := unitCoeff X e.inv
  val_inv := by
    rw [← unitCoeff_comp, e.hom_inv_id, unitCoeff_id]
  inv_val := by
    rw [← unitCoeff_comp, e.inv_hom_id, unitCoeff_id]

@[simp] theorem unitOfIso_val (e : unitModule X ≅ unitModule X) :
    (unitOfIso X e : Γ(X, ⊤)) = unitCoeff X e.hom := rfl

@[simp] theorem unitOfIso_unitIsoOfUnit (s : Γ(X, ⊤)ˣ) :
    unitOfIso X (unitIsoOfUnit X s) = s := by
  apply Units.ext
  exact unitCoeff_unitMul X s

@[simp] theorem unitIsoOfUnit_unitOfIso (e : unitModule X ≅ unitModule X) :
    unitIsoOfUnit X (unitOfIso X e) = e := by
  apply Iso.ext
  exact (unitHom_eq_unitMul X e.hom).symm

theorem unitOfIso_trans (e e' : unitModule X ≅ unitModule X) :
    unitOfIso X (e ≪≫ e') = unitOfIso X e * unitOfIso X e' := by
  apply Units.ext
  exact unitCoeff_comp X e.hom e'.hom

/-- Actual structure-module automorphisms are multiplicatively equivalent to
the units of the full ring of global functions. -/
def unitAutEquiv : Aut (unitModule X) ≃* Γ(X, ⊤)ˣ where
  toFun := unitOfIso X
  invFun := unitIsoOfUnit X
  left_inv := unitIsoOfUnit_unitOfIso X
  right_inv := unitOfIso_unitIsoOfUnit X
  map_mul' e e' := by
    change unitOfIso X (e' ≪≫ e) = _
    rw [unitOfIso_trans, mul_comm]

/-- Taking powers uses the same extracted coefficient for every degree. -/
theorem unitOfIso_pow (e : Aut (unitModule X)) (n : ℕ) :
    unitOfIso X (e ^ n) = unitOfIso X e ^ n :=
  map_pow (unitAutEquiv X) e n

theorem unitIsoOfUnit_pow (s : Γ(X, ⊤)ˣ) (n : ℕ) :
    unitIsoOfUnit X (s ^ n) = (unitIsoOfUnit X s : Aut (unitModule X)) ^ n :=
  map_pow (unitAutEquiv X).symm s n

theorem unitIsoOfUnit_pow_app (s : Γ(X, ⊤)ˣ) (n : ℕ)
    (U : X.Opens) (a : Γ(X, U)) :
    (unitIsoOfUnit X (s ^ n)).hom.app U a = a * (res le_top (s : Γ(X, ⊤))) ^ n := by
  change a * res le_top ((s ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) = _
  simp

end

end ArithDyn.Extension.ProjTwist
