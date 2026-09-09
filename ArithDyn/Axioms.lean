import ArithDyn.Density.Main
import ArithDyn.Density.Zariski
import ArithDyn.Nilpotence.Main
import ArithDyn.Derksen.Normal
import ArithDyn.Derksen.FundRec
import ArithDyn.Derksen.Decomposition
import ArithDyn.Derksen.Descent
import ArithDyn.Nilpotence.EliminationOpen
import ArithDyn.Nilpotence.Irreducible
import ArithDyn.Nilpotence.Monomial
import ArithDyn.Nilpotence.Curves
import ArithDyn.Extension.Inseparable
import ArithDyn.Extension.SeparableDescent
import ArithDyn.Derksen.RatFuncGalois
import ArithDyn.Derksen.Reconstruct
import ArithDyn.Derksen.ValuationPoint
import ArithDyn.Derksen.CoeffDescent
import ArithDyn.Derksen.Grouping
import ArithDyn.Derksen.BackwardAux
import ArithDyn.Extension.Veronese
import ArithDyn.Extension.Avoidance
import ArithDyn.Extension.ExtendCore
import ArithDyn.Extension.Theorem31
import ArithDyn.Extension.Iterates
import ArithDyn.Derksen.Torus
import ArithDyn.Derksen.TorusBackward
import ArithDyn.Derksen.Prop26

/-! Axiom audit: every main statement must depend only on `propext`, `Classical.choice`, `Quot.sound`. -/

-- §4: Theorem 4.2 and Corollary 4.9
#print axioms ArithDyn.Density.indet_iff
#print axioms ArithDyn.Density.not_regularAt_O
#print axioms ArithDyn.Density.not_regularAt_E
#print axioms ArithDyn.Density.not_regularAt_F
#print axioms ArithDyn.Density.Fpoly_isHomogeneous
#print axioms ArithDyn.Density.g_f_eq
#print axioms ArithDyn.Density.f_g_eq
#print axioms ArithDyn.Density.totallyDefined_iff_forall_mem_D
#print axioms ArithDyn.Density.card_totallyDefined'
#print axioms ArithDyn.Density.exact_count_galoisField
#print axioms ArithDyn.Density.liminf_density
#print axioms ArithDyn.Density.limsup_density
#print axioms ArithDyn.Density.density_not_convergent
#print axioms ArithDyn.Density.liminf_density_galoisField
#print axioms ArithDyn.Density.limsup_density_galoisField
#print axioms ArithDyn.Density.liminf_density_two_galoisField
#print axioms ArithDyn.Density.not_tendsto_one_galoisField
#print axioms ArithDyn.Density.prop_4_10
-- §5: Theorem 5.2
#print axioms ArithDyn.Nilpotence.fixed_iff
#print axioms ArithDyn.Nilpotence.T_T_eq_zero_of_not_inU
#print axioms ArithDyn.Nilpotence.Ysurf_reaches_zero
#print axioms ArithDyn.Nilpotence.exists_Ysurf_iterate_ne_zero
#print axioms ArithDyn.Nilpotence.eq_zero_of_vanish_on_Eset
#print axioms ArithDyn.Nilpotence.exists_vanishing_poly
#print axioms ArithDyn.Nilpotence.no_universal_seed
#print axioms ArithDyn.Nilpotence.no_universal_seed'
#print axioms ArithDyn.Nilpotence.theorem_5_2
#print axioms ArithDyn.Nilpotence.curveSet_injective
-- §5: locally closed `Y = V F \ V G` (UFD variant of the elimination)
#print axioms ArithDyn.Nilpotence.exists_vanishing_poly_open
#print axioms ArithDyn.Nilpotence.exists_vanishing_poly_locallyClosed
#print axioms ArithDyn.Nilpotence.no_universal_seed_locallyClosed
#print axioms ArithDyn.Nilpotence.no_universal_seed_locallyClosed'
#print axioms ArithDyn.Nilpotence.theorem_5_2_locallyClosed
-- §5: Lemma 5.6, irreducibility of `Y_s`
#print axioms ArithDyn.Nilpotence.irreducible_fs
#print axioms ArithDyn.Nilpotence.prime_fs
#print axioms ArithDyn.Nilpotence.vanishingIdeal_Ysurf
#print axioms ArithDyn.Nilpotence.isPrime_vanishingIdeal_Ysurf
#print axioms ArithDyn.Nilpotence.Ysurf_irreducible
#print axioms ArithDyn.Nilpotence.theorem_5_2'
-- §5: Proposition 5.11 (monomial criterion)
#print axioms ArithDyn.Nilpotence.geomNilpotent_closure_monoCone_zero
#print axioms ArithDyn.Nilpotence.geomNilpotent_monoCone_of_prime_pow
#print axioms ArithDyn.Nilpotence.not_geomNilpotent_monoCone
#print axioms ArithDyn.Nilpotence.geomNilpotent_closure_monoCone_iff
#print axioms ArithDyn.Nilpotence.prop_5_11
-- §3: Example 3.5 and Lemma 3.4 (separable descent, linear-algebra core)
#print axioms ArithDyn.Extension.G_nontrivial_zero
#print axioms ArithDyn.Extension.exists_restrictScalars
#print axioms ArithDyn.Extension.separable_descent_zero
#print axioms ArithDyn.Extension.isHomogeneous_restrictScalars
-- §2: linear recurrences, Lemma 2.3 (partial), and the reduction Theorem 2.2 ⇐ Proposition 2.7
#print axioms ArithDyn.Derksen.isLinRecSeq_iff
#print axioms ArithDyn.Derksen.RClass.union_mem
#print axioms ArithDyn.Derksen.RClass.affine_preimage_mem
#print axioms ArithDyn.Derksen.RClass.singleton_mem_ratFunc
#print axioms ArithDyn.Derksen.theorem22_of_prop27
#print axioms ArithDyn.Derksen.isFundRec_iff_exists_rep
#print axioms ArithDyn.Derksen.RClass.affine_image_mem
-- §2: Proposition 2.7 ⇐ Proposition 2.6 (circle-gap decomposition), hence Theorem 2.2 ⇐ Proposition 2.6
#print axioms ArithDyn.Derksen.exists_gap
#print axioms ArithDyn.Derksen.Eset_eq_iUnion_faces
#print axioms ArithDyn.Derksen.prop27_of_prop26
#print axioms ArithDyn.Derksen.theorem22_of_prop26
-- §2: Lemma 2.4 (Galois descent of fundamental recurrences)
#print axioms ArithDyn.Derksen.IsFundRec.norm
#print axioms ArithDyn.Derksen.RClass.descent
#print axioms ArithDyn.Derksen.IsLinRecSeq.norm
-- §2: rational function fields: Galois descent, intersections (towards Proposition 2.6)
#print axioms ArithDyn.Derksen.RClass.descent_ratFunc
#print axioms ArithDyn.Derksen.RClass.finset_iInter_mem_ratFunc
-- §2: Lemma 2.5 (Frobenius reconstruction)
#print axioms ArithDyn.Derksen.fk_irreducible
#print axioms ArithDyn.Derksen.star_identity
#print axioms ArithDyn.Derksen.reconstruct_aux
#print axioms ArithDyn.Derksen.reconstruct
-- §2: tools for Proposition 2.6 (valuation-ring point, coefficient descent, grouping)
#print axioms ArithDyn.Derksen.exists_valuationSubring_of_ringHom
#print axioms ArithDyn.Derksen.exists_common_field
#print axioms ArithDyn.Derksen.exists_coeff_descent
#print axioms ArithDyn.Derksen.coeff_descent_eq
#print axioms ArithDyn.Derksen.group_weights
#print axioms ArithDyn.Derksen.exists_exponents
#print axioms ArithDyn.Derksen.exists_compositum
-- §3: Veronese combinatorics and prime avoidance / height induction (towards Theorem 3.1)
#print axioms ArithDyn.Extension.exists_rewrite_verMon
#print axioms ArithDyn.Extension.exists_verMap_of_quadrics
#print axioms ArithDyn.Extension.exists_add_mem_radical
#print axioms ArithDyn.Extension.exists_extension_core
#print axioms ArithDyn.Extension.exists_extension_core'
-- §3: Theorem 3.1 (concrete form: X = V(I) ⊆ ℙ^r, L = O_X(1), φ given by forms of degree d)
#print axioms ArithDyn.Extension.theorem_3_1
#print axioms ArithDyn.Extension.theorem_3_1_iterates
-- §2: the torus ideal, forward direction of (2.x), recurrences `n ↦ f(Pⁿ)`
#print axioms ArithDyn.Derksen.aeval_Pn_eq_zero_of_mem_torusIdeal
#print axioms ArithDyn.Derksen.isFundRec_aeval_Pn
-- §2: backward direction of (2.x), Proposition 2.6, Proposition 2.7, Theorem 2.2 (unconditional)
#print axioms ArithDyn.Derksen.mem_Eset_of_aeval_Pn_eq_zero
#print axioms ArithDyn.Derksen.Eset_mem_RClass_ratFunc
#print axioms ArithDyn.Derksen.prop26
#print axioms ArithDyn.Derksen.prop27
#print axioms ArithDyn.Derksen.theorem22
