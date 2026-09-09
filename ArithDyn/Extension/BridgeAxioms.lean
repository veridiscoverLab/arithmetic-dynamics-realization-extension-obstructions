import ArithDyn.Extension.SectionLifting
import ArithDyn.Extension.HomogeneousCoordinates
import ArithDyn.Extension.QuotientDynamics
import ArithDyn.Extension.NilpotentRegression
import ArithDyn.Extension.ProjRadical
import ArithDyn.Extension.ProjMapLaws
import ArithDyn.Extension.DegreeMap
import ArithDyn.Extension.ProjClosedImmersion
import ArithDyn.Extension.ProjOverBase
import ArithDyn.Extension.GradedQuotient
import ArithDyn.Extension.QuotientDegreeMap
import ArithDyn.Extension.ProjRegradingCore
import ArithDyn.Extension.ProjRegrading

/-!
# Axiom audit for the extension bridges

These declarations audit the implemented interfaces, not a theorem from arbitrary
polarized schemes.  In particular, the section-restriction surjectivity premise and
the constantly weighted target of `degreeMap` remain visible in their actual types.
-/

#print axioms ArithDyn.Extension.aeval_mem_graded_piece_of_degree
#print axioms ArithDyn.Extension.section_restriction_kernel_isHomogeneous
#print axioms ArithDyn.Extension.exists_lifts_of_veronese_restriction_surjective
#print axioms ArithDyn.Extension.coordinate_lifts_commute
#print axioms ArithDyn.Extension.coordinate_lifts_preserve_kernel
#print axioms ArithDyn.Extension.coordinate_lifts_nonvanishing
#print axioms ArithDyn.Extension.exists_polarized_lifts_with_homogeneous_kernel

#print axioms ArithDyn.Extension.coordinateIdeal_le_radical_of_no_basepoint
#print axioms ArithDyn.Extension.coordinateIdeal_le_radical_of_global_no_basepoint
#print axioms ArithDyn.Extension.exists_coordinateIdeal_pow_le
#print axioms ArithDyn.Extension.exists_degree_bound_mem_equations_and_coordinates
#print axioms ArithDyn.Extension.span_evaluated_coordinates_eq_top
#print axioms ArithDyn.Extension.standard_irrelevant_eq_coordinateIdeal

#print axioms ArithDyn.Extension.quotientEnd
#print axioms ArithDyn.Extension.quotient_commuting_square
#print axioms ArithDyn.Extension.quotientEnd_iterMap
#print axioms ArithDyn.Extension.quotient_commuting_square_iterates
#print axioms ArithDyn.Extension.specMap_algHom_over_base
#print axioms ArithDyn.Extension.specMap_algHom_pow
#print axioms ArithDyn.Extension.quotientSpec_commuting_square
#print axioms ArithDyn.Extension.quotientSpec_commuting_square_powers

#print axioms ArithDyn.Extension.NilpotentRegression.epsilon_ne_zero
#print axioms ArithDyn.Extension.NilpotentRegression.epsilon_sq_zero
#print axioms ArithDyn.Extension.NilpotentRegression.quotient_endomorphisms_distinct
#print axioms ArithDyn.Extension.NilpotentRegression.spectrum_endomorphisms_distinct
#print axioms ArithDyn.Extension.NilpotentRegression.same_on_all_field_points

#print axioms AlgebraicGeometry.Proj.mapRadical
#print axioms AlgebraicGeometry.Proj.localRingHom_comp_stalkIsoRadical
#print axioms AlgebraicGeometry.Proj.mapRadical_preimage_basicOpen
#print axioms AlgebraicGeometry.Proj.awayι_comp_mapRadical
#print axioms AlgebraicGeometry.Proj.mapRadical_eq_map
#print axioms AlgebraicGeometry.Proj.affineOpenCoverOfIrrelevantLERadical
#print axioms AlgebraicGeometry.Proj.irrelevant_le_radical_map_comp
#print axioms AlgebraicGeometry.Proj.mapRadical_comp
#print axioms AlgebraicGeometry.Proj.mapRadical_id

#print axioms ArithDyn.Extension.weighted_aeval_isHomogeneous
#print axioms ArithDyn.Extension.degreeSubstitution
#print axioms ArithDyn.Extension.degreeMapOfRadical
#print axioms ArithDyn.Extension.degreeMap
#print axioms ArithDyn.Extension.degreeMapOfRadical_preimage_basicOpen

#print axioms ArithDyn.Extension.exists_homogeneous_preimage
#print axioms ArithDyn.Extension.irrelevant_le_map_of_surjective
#print axioms ArithDyn.Extension.away_map_surjective
#print axioms ArithDyn.Extension.proj_map_restrict_isClosedImmersion
#print axioms ArithDyn.Extension.proj_map_isClosedImmersion
#print axioms ArithDyn.Extension.proj_map_isClosedImmersion_of_surjective

#print axioms AlgebraicGeometry.Proj.away_map_comp_fromZeroRingHom
#print axioms AlgebraicGeometry.Proj.mapRadical_toSpecZero

#print axioms ArithDyn.Extension.GradedQuotient.ideal_le_ker_decompose
#print axioms ArithDyn.Extension.GradedQuotient.decomposeQuotient_left_inv
#print axioms ArithDyn.Extension.GradedQuotient.decomposeQuotient_right_inv
#print axioms ArithDyn.Extension.GradedQuotient.quotientGradedAlgebra
#print axioms ArithDyn.Extension.GradedQuotient.quotientGradedMap_surjective
#print axioms ArithDyn.Extension.GradedQuotient.quotientGradedMap_ker
#print axioms ArithDyn.Extension.GradedQuotient.quotient_decompose_mk
#print axioms ArithDyn.Extension.GradedQuotient.quotient_proj_isClosedImmersion

#print axioms ArithDyn.Extension.polynomialQuotientGradedAlgebra
#print axioms ArithDyn.Extension.quotientDegreeSubstitution
#print axioms ArithDyn.Extension.quotient_irrelevant_le_radical_map
#print axioms ArithDyn.Extension.quotientDegreeMapOfRadical
#print axioms ArithDyn.Extension.quotientDegreeMap

#print axioms ArithDyn.Extension.constant_weight_eq
#print axioms ArithDyn.Extension.localizationConstantWeightEquiv
#print axioms ArithDyn.Extension.constantWeight_irrelevant_eq
#print axioms ArithDyn.Extension.constantWeightHomeomorph
#print axioms ArithDyn.Extension.sectionFromConstantWeight
#print axioms ArithDyn.Extension.sectionToConstantWeight

#print axioms ArithDyn.Extension.constantWeightSheafedSpaceIso
#print axioms ArithDyn.Extension.constantWeightProjIso
#print axioms ArithDyn.Extension.standardDegreeMap
#print axioms ArithDyn.Extension.standardDegreeMap_preimage_basicOpen
#print axioms ArithDyn.Extension.quotientStandardDegreeMapOfRadical
#print axioms ArithDyn.Extension.quotientStandardDegreeMap
#print axioms ArithDyn.Extension.quotientStandardDegreeMap_preimage_basicOpen
