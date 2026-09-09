import ArithDyn.Extension.Theorem31Projective
import ArithDyn.Extension.SectionAlgebraMaps
import ArithDyn.Extension.SectionAlgebraPullback
import ArithDyn.Extension.SectionAlgebraAdjunction
import ArithDyn.Extension.PolarizationUnit
import ArithDyn.Extension.ProjTwistAxioms
import ArithDyn.Extension.ProjCoordinateBasis
import ArithDyn.Extension.ScaledProjRegradingSections
import ArithDyn.Extension.PolarizedSectionDynamics

/-!
# Audit of the concrete projective endpoint and actual section/sheaf bridges

These audits verify kernel dependencies.  The original ample-scheme entry,
restriction-surjectivity `hres`, and any still unproved polarization identification
are not removed by an axiom audit.  See docs/FORMALIZATION.md for the exact scope.
-/

#print axioms ArithDyn.Extension.DegreeScaledHom.map_proj
#print axioms ArithDyn.Extension.DegreeScaledHom.idealComap
#print axioms ArithDyn.Extension.DegreeScaledHom.localizationMap
#print axioms ArithDyn.Extension.DegreeScaledHom.localizationMap_comp
#print axioms ArithDyn.Extension.DegreeScaledHom.projMap
#print axioms ArithDyn.Extension.DegreeScaledHom.projMap_comp
#print axioms ArithDyn.Extension.DegreeScaledHom.projMap_congr
#print axioms ArithDyn.Extension.scaledPolynomialProjMap
#print axioms ArithDyn.Extension.scaledQuotientCoordinateProjMap
#print axioms ArithDyn.Extension.scaledQuotientEndProjMap
#print axioms ArithDyn.Extension.scaledOfWeighted_localRingHom
#print axioms ArithDyn.Extension.scaledOfWeighted_sectionMap
#print axioms ArithDyn.Extension.veronese_away_map_surjective
#print axioms ArithDyn.Extension.quotientStandardDegreeMap_isClosedImmersion_of_exact_veronese
#print axioms ArithDyn.Extension.scaledQuotientCoordinateProjMap_isClosedImmersion_of_exact_veronese
#print axioms ArithDyn.Extension.scaledProj_commuting_square
#print axioms ArithDyn.Extension.scheme_commuting_square_powers
#print axioms ArithDyn.Extension.theorem_3_1_projective
#print axioms ArithDyn.Extension.exact_veronese_no_basepoint
#print axioms ArithDyn.Extension.quotientCoordinateInclusion_comp
#print axioms ArithDyn.Extension.quotientCoordinatePolarizationIso
#print axioms ArithDyn.Extension.ProjTwist.scaledPolynomialPolarizationIso
#print axioms ArithDyn.Extension.ProjTwist.pullbackTwistedIso

#print axioms ArithDyn.Extension.ProjTwist.standardCocycle
#print axioms ArithDyn.Extension.ProjTwist.standardO
#print axioms ArithDyn.Extension.ProjTwist.standardO_localPullbackIso
#print axioms ArithDyn.Extension.ProjTwist.constantWeightCoordinateTwist
#print axioms ArithDyn.Extension.ProjTwist.homogeneousBasisSection
#print axioms ArithDyn.Extension.ProjTwist.homogeneousBasisLinearEquiv
#print axioms ArithDyn.Extension.ProjTwist.homogeneousBasisPullbackIso
#print axioms ArithDyn.Extension.ProjTwist.pullbackCocycle
#print axioms ArithDyn.Extension.ProjTwist.pullbackSections_smul
#print axioms ArithDyn.Extension.ProjTwist.pullbackSections_mul
#print axioms ArithDyn.Extension.ProjTwist.sectionAlgebraPullback
#print axioms ArithDyn.Extension.ProjTwist.sectionAlgebraPullback_restrict
#print axioms ArithDyn.Extension.ProjTwist.pullbackSectionsHom
#print axioms ArithDyn.Extension.SectionAlgebra.sectionGradingOn
#print axioms ArithDyn.Extension.SectionAlgebra.sectionInclusion_mul
#print axioms ArithDyn.Extension.SectionAlgebra.sheafSectionAlgebraOn_eq
#print axioms ArithDyn.Extension.SectionAlgebra.sectionRestriction_comp
#print axioms ArithDyn.Extension.SectionAlgebra.degreeZeroEquiv

#print axioms ArithDyn.Extension.SectionAlgebra.mapOnSections
#print axioms ArithDyn.Extension.SectionAlgebra.mapOnSections_eq_pullback
#print axioms ArithDyn.Extension.SectionAlgebra.polarizedOnSections
#print axioms ArithDyn.Extension.SectionAlgebra.baseRingHom_naturality
#print axioms ArithDyn.Extension.SectionAlgebra.mapOnGlobalSectionsOver
#print axioms ArithDyn.Extension.SectionAlgebra.adjoint_pullbackComp
#print axioms ArithDyn.Extension.SectionAlgebra.adjoint_restrictIso
#print axioms ArithDyn.Extension.ProjTwist.unitHom_eq_unitMul
#print axioms ArithDyn.Extension.ProjTwist.unitAutEquiv
#print axioms ArithDyn.Extension.ProjTwist.unitOfIso_pow
#print axioms ArithDyn.Extension.ProjTwist.unitIsoOfUnit_pow_app

#print axioms ArithDyn.Extension.SectionAlgebra.sectionBaseAlgebra
#print axioms ArithDyn.Extension.SectionAlgebra.sectionBaseScalarTower
#print axioms ArithDyn.Extension.SectionAlgebra.sectionGradingOverBase
#print axioms ArithDyn.Extension.SectionAlgebra.sectionGradingOverBase_graded
#print axioms ArithDyn.Extension.SectionAlgebra.sectionEndOverBase
#print axioms ArithDyn.Extension.ProjTwist.polarizationAlgebraHom
#print axioms ArithDyn.Extension.ProjTwist.polarizationAlgebraHom_mem
#print axioms ArithDyn.Extension.ProjTwist.polarizationAlgebraHom_degree_one
#print axioms ArithDyn.Extension.ProjTwist.polarizationAlgebraHom_restrict
#print axioms ArithDyn.Extension.ProjTwist.polarizedAlgebraEnd
#print axioms ArithDyn.Extension.ProjTwist.polarizedAlgebraEnd_mem
#print axioms ArithDyn.Extension.ProjTwist.polarizedAlgebraEnd_degree_one
#print axioms ArithDyn.Extension.ProjTwist.polarizedAlgebraEnd_algebraMap
#print axioms ArithDyn.Extension.ProjTwist.polarizedAlgebraEnd_eq_power_sections
#print axioms ArithDyn.Extension.ProjTwist.polarizedAlgebraEndOverBase
#print axioms ArithDyn.Extension.ProjTwist.polarizedAlgebraEndOverBase_mem
