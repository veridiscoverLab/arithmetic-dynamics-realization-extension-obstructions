import ArithDyn.Nilpotence.Main

/-!
# The monomial criterion (paper §5.5, Proposition 5.11)

For coprime integers `a, b` let `V_{a,b}` be the Zariski closure of the cone
`{(t^a z, t^b z, z) : t, z ∈ K^×} ⊆ 𝔸³_K`.

* If `a = 0`, then `V_{0,b} ⊆ {x = z}` reaches `O` in one step.
* If `a ≠ 0` and `K = \bar 𝔽_p`, then `V_{a,b}` is geometrically nilpotent iff `|a|` is a power
  of `p`.

The closure meets the torus `U` exactly in the cone (Bezout: the image of `t ↦ (t^a, t^b)` is the
curve `u^b = v^a`), and points outside `U` reach `O` in two steps, so geometric nilpotency of the
closure is that of the cone. On the cone the orbit formula `Tⁿ(uz, vz, z) = (u zₙ, uⁿ v zₙ, zₙ)`
with `u = t^a`, `v = t^b` reduces everything to whether `t^{a n + b} = 1` for some `n ≥ 0`:
* if `|a| = p^s`, then `a` is invertible modulo the (prime-to-`p`) order of `t`, so such `n`
  exists;
* if a prime `ℓ ≠ p` divides `a`, a primitive `ℓ^{v_ℓ(a)+1}`-th root of unity `t` gives a point
  `(t^a, t^b, 1)` of the cone whose orbit never leaves `U`.
-/

set_option autoImplicit false

namespace ArithDyn.Nilpotence

open MvPolynomial

variable {K : Type*} [Field K]

/-- The cone `{(t^a z, t^b z, z) : t, z ∈ K^×}` (integer exponents, `zpow`). -/
def monoCone (a b : ℤ) : Set (Fin 3 → K) :=
  {y | ∃ t z : K, t ≠ 0 ∧ z ≠ 0 ∧ y = ![t ^ a * z, t ^ b * z, z]}

/-! ### The case `a = 0` -/

/-- `a = 0`: the closure lies in `{x = z}` and reaches `O` in one step. -/
theorem T_eq_zero_of_mem_closure_monoCone_zero (b : ℤ) :
    ∀ y ∈ zariskiClosure (monoCone (K := K) 0 b), T y = 0 := by
  intro y hy
  have hxz : y 0 = y 2 := by
    have h := hy (X 0 - X 2) ?_
    · simpa [sub_eq_zero] using h
    · rintro _ ⟨t, z, -, -, rfl⟩
      simp
  ext i; fin_cases i <;> simp [T, Dq, hxz]

theorem geomNilpotent_closure_monoCone_zero (b : ℤ) :
    GeomNilpotent (zariskiClosure (monoCone (K := K) 0 b)) :=
  ⟨0, T_zero, fun y hy => ⟨1, le_rfl, by
    rw [Function.iterate_one]; exact T_eq_zero_of_mem_closure_monoCone_zero b y hy⟩⟩

/-! ### Arithmetic: solving `a n + b ≡ 0 (mod M)` with `n ≥ 0` -/

/-- If `gcd(a, M) = 1` and `M > 0`, then `a n + b ≡ 0 (mod M)` has a solution `n ∈ ℕ`. -/
lemma exists_nat_dvd_mul_add {a b M : ℤ} (hM : 0 < M) (hgcd : Int.gcd a M = 1) :
    ∃ n : ℕ, M ∣ a * n + b := by
  have hbez : a * Int.gcdA a M + M * Int.gcdB a M = 1 := by
    have := (Int.gcd_eq_gcd_ab a M).symm
    rwa [hgcd, Nat.cast_one] at this
  obtain ⟨n, -, hn⟩ := Int.existsUnique_equiv_nat (-b * Int.gcdA a M) hM
  refine ⟨n, ?_⟩
  have h1 : a * n + b ≡ a * (-b * Int.gcdA a M) + b [ZMOD M] := (hn.mul_left a).add_right b
  have h2 : a * (-b * Int.gcdA a M) + b = M * (b * Int.gcdB a M) := by
    linear_combination (-b) * hbez
  rw [← Int.modEq_zero_iff_dvd]
  refine h1.trans ?_
  rw [h2]
  exact Int.modEq_zero_iff_dvd.2 (dvd_mul_right _ _)

/-! ### `|a| = p^s`: the cone is geometrically nilpotent -/

/-- `|a| = p^s` ⟹ geometrically nilpotent (any field in which nonzero elements have finite order
coprime to `p`). -/
theorem geomNilpotent_monoCone_of_prime_pow {p : ℕ} (hp : p.Prime)
    (hfin : ∀ u : K, u ≠ 0 → ∃ M : ℕ, 0 < M ∧ Nat.Coprime M p ∧ u ^ M = 1)
    {a b : ℤ} {s : ℕ} (ha : a.natAbs = p ^ s) : GeomNilpotent (monoCone (K := K) a b) := by
  refine ⟨0, T_zero, ?_⟩
  rintro _ ⟨t, z, ht, hz, rfl⟩
  obtain ⟨M, hM, hcop, htM⟩ := hfin t ht
  -- `gcd(a, M) = 1` since `|a| = p^s` and `gcd(M, p) = 1`
  have hgcd : Int.gcd a (M : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, ha]
    exact Nat.Coprime.pow_left s hcop.symm
  obtain ⟨n, hn⟩ := exists_nat_dvd_mul_add (b := b) (by exact_mod_cast hM) hgcd
  refine ⟨n + 1, by omega, ?_⟩
  rw [iterate_T_scaled]
  -- `vₙ = uⁿ v = t^{a n + b} = 1`, so `z_{n+1} = 0`
  have hzn : zseq (t ^ a) (t ^ b) z (n + 1) = 0 := by
    rw [zseq_succ]
    have h1 : (t ^ a) ^ n * t ^ b = 1 := by
      obtain ⟨k, hk⟩ := hn
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ ht, hk, zpow_mul, zpow_natCast, htM, one_zpow]
    rw [h1, sub_self, mul_zero, zero_mul, zero_mul]
  rw [hzn]
  ext i; fin_cases i <;> simp

/-! ### `|a|` not a power of `p`: an escaping point of the cone -/

/-- A primitive root statement for `t^{|a|}` transfers to `t^a` (`zpow`). -/
lemma isPrimitiveRoot_zpow_of_natAbs {t : K} {k : ℕ} {a : ℤ}
    (h : IsPrimitiveRoot (t ^ a.natAbs) k) : IsPrimitiveRoot (t ^ a) k := by
  rcases Int.natAbs_eq a with ha | ha
  · rw [ha, zpow_natCast]; exact h
  · rw [ha, zpow_neg, zpow_natCast]; exact h.inv

/-- `|a|` not a power of `p` (and `gcd(a,b) = 1`, `a ≠ 0`) ⟹ not geometrically nilpotent. -/
theorem not_geomNilpotent_monoCone [IsAlgClosed K] {p : ℕ} [CharP K p] (hp : p.Prime)
    {a b : ℤ} (hcop : Int.gcd a b = 1) (ha : a ≠ 0) (hnot : ∀ s : ℕ, a.natAbs ≠ p ^ s) :
    ¬ GeomNilpotent (monoCone (K := K) a b) := by
  intro hnil
  have ha0 : a.natAbs ≠ 0 := Int.natAbs_ne_zero.2 ha
  -- a prime `ℓ ≠ p` dividing `|a|`
  obtain ⟨ℓ, hℓ, hℓa, hℓp⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ a.natAbs ∧ ℓ ≠ p := by
    by_contra hcon
    exact hnot _ (Nat.eq_prime_pow_of_unique_prime_dvd ha0
      (fun {d} hd hdvd => by_contra (fun hne => hcon ⟨d, hd, hdvd, hne⟩)))
  -- `|a| = ℓ^e * a'` with `ℓ ∤ a'`; necessarily `e ≥ 1`
  obtain ⟨e, a', hnd, hdecomp⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha0 ℓ hℓ.ne_one
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hdecomp
    rw [hdecomp] at hℓa
    exact hnd hℓa
  -- a primitive `ℓ^(e+1)`-th root of unity `t` (exists since `ℓ ≠ p` and `K` is algebraically
  -- closed)
  have hN0 : ℓ ^ (e + 1) ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  haveI : NeZero ((ℓ ^ (e + 1) : ℕ) : K) := ⟨fun h => by
    have hpN : p ∣ ℓ ^ (e + 1) := (CharP.cast_eq_zero_iff K p _).1 h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hpN)).symm⟩
  haveI : IsCyclotomicExtension {ℓ ^ (e + 1)} K K :=
    IsSepClosed.isCyclotomicExtension {ℓ ^ (e + 1)} K (fun m hm _ => by
      rw [Set.mem_singleton_iff.1 hm]; infer_instance)
  obtain ⟨t, ht⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot K K (Set.mem_singleton (ℓ ^ (e + 1))) hN0
  have ht0 : t ≠ 0 := ht.ne_zero hN0
  -- `u = t^a` is a primitive `ℓ`-th root of unity
  have hu : IsPrimitiveRoot (t ^ a) ℓ := by
    apply isPrimitiveRoot_zpow_of_natAbs
    have h1 : IsPrimitiveRoot (t ^ ℓ ^ e) (ℓ ^ (e + 1) / ℓ ^ e) :=
      ht.pow_of_dvd (pow_ne_zero _ hℓ.ne_zero) (pow_dvd_pow ℓ (Nat.le_add_right e 1))
    have h2 : ℓ ^ (e + 1) / ℓ ^ e = ℓ := by
      rw [Nat.pow_div (Nat.le_add_right e 1) hℓ.pos, Nat.add_sub_cancel_left, pow_one]
    rw [h2] at h1
    have h3 := h1.pow_of_coprime a' ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hnd).symm
    rwa [← pow_mul, ← hdecomp] at h3
  -- `v = t^b` is a primitive `ℓ^(e+1)`-th root of unity (as `ℓ ∤ b`)
  have hv : IsPrimitiveRoot (t ^ b) (ℓ ^ (e + 1)) := by
    apply isPrimitiveRoot_zpow_of_natAbs
    apply ht.pow_of_coprime
    have hab : Nat.Coprime a.natAbs b.natAbs := hcop
    exact (Nat.Coprime.pow_left (e + 1) (Nat.Coprime.coprime_dvd_left hℓa hab)).symm
  have hu0 : t ^ a ≠ 0 := zpow_ne_zero a ht0
  have hv0 : t ^ b ≠ 0 := zpow_ne_zero b ht0
  have hu1 : t ^ a ≠ 1 := hu.ne_one hℓ.one_lt
  -- `uⁿ v ≠ 1` for all `n`: otherwise `v^ℓ = 1`, i.e. `ℓ^(e+1) ∣ ℓ`
  have hesc : ∀ n : ℕ, (t ^ a) ^ n * t ^ b ≠ 1 := by
    intro n hn
    have h1 : (t ^ b) ^ ℓ = 1 := by
      have h : ((t ^ a) ^ n * t ^ b) ^ ℓ = 1 ^ ℓ := by rw [hn]
      rwa [mul_pow, ← pow_mul, mul_comm n ℓ, pow_mul, hu.pow_eq_one, one_pow, one_pow,
        one_mul] at h
    have h2 : ℓ ^ (e + 1) ≤ ℓ := Nat.le_of_dvd hℓ.pos ((hv.pow_eq_one_iff_dvd ℓ).1 h1)
    have h3 : ℓ < ℓ ^ (e + 1) := by
      calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
        _ < ℓ ^ (e + 1) := Nat.pow_lt_pow_right hℓ.one_lt (by omega)
    exact absurd h2 (not_le.2 h3)
  -- the point `(u, v, 1)` of the cone never reaches `O`
  have hmem : (![t ^ a * 1, t ^ b * 1, 1] : Fin 3 → K) ∈ monoCone a b :=
    ⟨t, 1, ht0, one_ne_zero, rfl⟩
  obtain ⟨n, -, hn⟩ := hnil.reach_zero _ hmem
  exact iterate_ne_zero_of_escaping hu0 hv0 hu1 hesc one_ne_zero n hn

/-! ### The closure meets `U` exactly in the cone -/

/-- The binomial `x^{b⁺} y^{a⁻} z^{a⁺+b⁻} - y^{a⁺} x^{b⁻} z^{b⁺+a⁻}` (where `a = a⁺ - a⁻`,
`b = b⁺ - b⁻`), which cuts out the cone inside `U`. -/
noncomputable def monoPoly (a b : ℤ) : MvPolynomial (Fin 3) K :=
  X 0 ^ b.toNat * X 1 ^ (-a).toNat * X 2 ^ (a.toNat + (-b).toNat) -
    X 1 ^ a.toNat * X 0 ^ (-b).toNat * X 2 ^ (b.toNat + (-a).toNat)

lemma eval_monoPoly_scaled (a b : ℤ) (u v z : K) :
    eval ![u * z, v * z, z] (monoPoly a b) =
      (u ^ b.toNat * v ^ (-a).toNat - v ^ a.toNat * u ^ (-b).toNat) *
        z ^ (a.toNat + (-a).toNat + b.toNat + (-b).toNat) := by
  simp only [monoPoly, map_sub, map_mul, map_pow, eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- For `u, v ≠ 0`: `u^{b⁺} v^{a⁻} = v^{a⁺} u^{b⁻}` iff `u^b = v^a`. -/
lemma pow_toNat_eq_iff {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (a b : ℤ) :
    u ^ b.toNat * v ^ (-a).toNat = v ^ a.toNat * u ^ (-b).toNat ↔ u ^ b = v ^ a := by
  have key : ∀ (ap an bp bn : ℕ), a = ap - an → b = bp - bn →
      (u ^ bp * v ^ an = v ^ ap * u ^ bn ↔ u ^ b = v ^ a) := by
    intro ap an bp bn ha hb
    subst ha hb
    rw [zpow_sub₀ hu, zpow_sub₀ hv, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
      div_eq_div_iff (pow_ne_zero _ hu) (pow_ne_zero _ hv)]
  exact key _ _ _ _ (Int.toNat_sub_toNat_neg a).symm (Int.toNat_sub_toNat_neg b).symm

/-- The closure meets `U` exactly in the cone. -/
theorem mem_monoCone_of_mem_closure {a b : ℤ} (hcop : Int.gcd a b = 1) :
    ∀ y ∈ zariskiClosure (monoCone (K := K) a b), inU y → y ∈ monoCone a b := by
  intro y hy hU
  obtain ⟨hx, hy1, hz⟩ := hU
  -- the binomial vanishes on the cone ...
  have hvan : ∀ s ∈ monoCone (K := K) a b, eval s (monoPoly a b) = 0 := by
    rintro _ ⟨t, z, ht, -, rfl⟩
    rw [eval_monoPoly_scaled]
    have h : (t ^ a) ^ b.toNat * (t ^ b) ^ (-a).toNat =
        (t ^ b) ^ a.toNat * (t ^ a) ^ (-b).toNat := by
      rw [pow_toNat_eq_iff (zpow_ne_zero a ht) (zpow_ne_zero b ht), ← zpow_mul, ← zpow_mul,
        mul_comm a b]
    rw [h, sub_self, zero_mul]
  -- ... hence at `y = (u z, v z, z)`, which gives `u^b = v^a`
  obtain ⟨u, hu⟩ : ∃ u : K, u = y 0 / y 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : K, v = y 1 / y 2 := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by rw [hu]; exact div_ne_zero hx hz
  have hv0 : v ≠ 0 := by rw [hv]; exact div_ne_zero hy1 hz
  have hy' : y = ![u * y 2, v * y 2, y 2] := by
    rw [hu, hv]; exact eq_scaled_of_ne_zero y hz
  have h0 : eval ![u * y 2, v * y 2, y 2] (monoPoly a b) = 0 := by
    rw [← hy']; exact hy _ hvan
  rw [eval_monoPoly_scaled, mul_eq_zero, sub_eq_zero] at h0
  have huv : u ^ b = v ^ a :=
    (pow_toNat_eq_iff hu0 hv0 a b).1 (h0.resolve_right (pow_ne_zero _ hz))
  -- Bezout: `a i + b j = 1`; then `t := u^i v^j` satisfies `t^a = u`, `t^b = v`
  obtain ⟨i, j, hbez⟩ : ∃ i j : ℤ, a * i + b * j = 1 := by
    refine ⟨Int.gcdA a b, Int.gcdB a b, ?_⟩
    have := (Int.gcd_eq_gcd_ab a b).symm
    rwa [hcop, Nat.cast_one] at this
  have hta : (u ^ i * v ^ j) ^ a = u := by
    have h1 : v ^ (j * a) = u ^ (b * j) := by
      rw [mul_comm j a, zpow_mul v a j, ← huv, ← zpow_mul]
    rw [mul_zpow, ← zpow_mul, ← zpow_mul, h1, ← zpow_add₀ hu0]
    have : i * a + b * j = 1 := by linear_combination hbez
    rw [this, zpow_one]
  have htb : (u ^ i * v ^ j) ^ b = v := by
    have h1 : u ^ (i * b) = v ^ (a * i) := by
      rw [mul_comm i b, zpow_mul u b i, huv, ← zpow_mul]
    rw [mul_zpow, ← zpow_mul, ← zpow_mul, h1, ← zpow_add₀ hv0]
    have : a * i + j * b = 1 := by linear_combination hbez
    rw [this, zpow_one]
  refine ⟨u ^ i * v ^ j, y 2, mul_ne_zero (zpow_ne_zero _ hu0) (zpow_ne_zero _ hv0), hz, ?_⟩
  rw [hta, htb]
  exact hy'

/-- Geometric nilpotency of the closure of the cone is that of the cone: points of the closure
outside `U` reach `O` in two steps (Lemma 5.3). -/
theorem geomNilpotent_closure_monoCone_iff {a b : ℤ} (hcop : Int.gcd a b = 1) :
    GeomNilpotent (zariskiClosure (monoCone (K := K) a b)) ↔
      GeomNilpotent (monoCone (K := K) a b) := by
  refine ⟨fun ⟨P, hP, h⟩ => ⟨P, hP, fun y hy => h y (subset_zariskiClosure _ hy)⟩, fun h => ?_⟩
  refine ⟨0, T_zero, fun y hy => ?_⟩
  by_cases hU : inU y
  · exact h.reach_zero y (mem_monoCone_of_mem_closure hcop y hy hU)
  · exact ⟨2, one_le_two, T_T_eq_zero_of_not_inU hU⟩

/-! ### Proposition 5.11 over `\bar 𝔽_p` -/

/-- **Proposition 5.11** over `\bar 𝔽_p`: for `gcd(a, b) = 1` and `a ≠ 0`, the closure of the
cone `{(t^a z, t^b z, z)}` is geometrically nilpotent iff `|a|` is a power of `p`. -/
theorem prop_5_11 (p : ℕ) [Fact p.Prime] {a b : ℤ} (hcop : Int.gcd a b = 1) (ha : a ≠ 0) :
    GeomNilpotent (zariskiClosure (monoCone (K := AlgebraicClosure (ZMod p)) a b)) ↔
      ∃ s : ℕ, a.natAbs = p ^ s := by
  rw [geomNilpotent_closure_monoCone_iff hcop]
  constructor
  · intro h
    by_contra hnot
    exact not_geomNilpotent_monoCone (K := AlgebraicClosure (ZMod p)) (p := p) Fact.out hcop ha
      (fun s hs => hnot ⟨s, hs⟩) h
  · rintro ⟨s, hs⟩
    exact geomNilpotent_monoCone_of_prime_pow (p := p) Fact.out
      (fun u hu => exists_pow_eq_one_coprime (p := p) u hu) hs

end ArithDyn.Nilpotence
