import ArithDyn.Extension.ProjTwistPullback
import ArithDyn.Extension.ProjTwistHomogeneous
import ArithDyn.Extension.ProjTwistReconstruction
import ArithDyn.Extension.ProjTwistRegrading
import ArithDyn.Extension.PolarizationGluing
import ArithDyn.Extension.PolarizationSheaf

/-! Kernel dependency audit of the actual cocycle sheaf and pullback bridge. -/

#print axioms ArithDyn.Extension.ProjTwist.sectionSubmodule
#print axioms ArithDyn.Extension.ProjTwist.restrictSections
#print axioms ArithDyn.Extension.ProjTwist.existsUnique_gluingSections
#print axioms ArithDyn.Extension.ProjTwist.presheaf_isSheaf
#print axioms ArithDyn.Extension.ProjTwist.twistedModule
#print axioms ArithDyn.Extension.ProjTwist.fromLocal
#print axioms ArithDyn.Extension.ProjTwist.localLinearEquiv
#print axioms ArithDyn.Extension.ProjTwist.toLocal_restrict
#print axioms ArithDyn.Extension.ProjTwist.localRestrictionIso
#print axioms ArithDyn.Extension.ProjTwist.localPullbackIso
#print axioms ArithDyn.Extension.ProjTwist.homogeneousRatio
#print axioms ArithDyn.Extension.ProjTwist.homogeneousRatio_self
#print axioms ArithDyn.Extension.ProjTwist.homogeneousRatio_comp
#print axioms ArithDyn.Extension.ProjTwist.homogeneousRatioUnit
#print axioms ArithDyn.Extension.ProjTwist.homogeneousCocycle
#print axioms ArithDyn.Extension.ProjTwist.isIso_of_restrictions
#print axioms ArithDyn.Extension.ProjTwist.opensMapFinal
#print axioms ArithDyn.Extension.ProjTwist.pullbackUnitIso
#print axioms ArithDyn.Extension.ProjTwist.inverseImageLocalIso
#print axioms ArithDyn.Extension.ProjTwist.inverseImageRestrictionIso
#print axioms ArithDyn.Extension.ProjTwist.pullbackComparison
#print axioms ArithDyn.Extension.ProjTwist.pullbackComparison_adjoint
#print axioms ArithDyn.Extension.ProjTwist.pullbackComparison_onSections
#print axioms ArithDyn.Extension.ProjTwist.pullbackSections_toLocal
#print axioms ArithDyn.Extension.ProjTwist.pullbackSections_fromLocal
#print axioms ArithDyn.Extension.ProjTwist.pullbackSections_basis
#print axioms ArithDyn.Extension.ProjTwist.comparisonLocalMatrix
#print axioms ArithDyn.Extension.ProjTwist.pullbackComparison_isIso_iff
#print axioms ArithDyn.Extension.ProjTwist.frameCoordinatesOnImage
#print axioms ArithDyn.Extension.ProjTwist.localFrameCoordinates
#print axioms ArithDyn.Extension.ProjTwist.localFrameCoordinates_restrict
#print axioms ArithDyn.Extension.ProjTwist.localFrameCoordinates_symm_restrict
#print axioms ArithDyn.Extension.ProjTwist.unitOfSelfLinearEquiv
#print axioms ArithDyn.Extension.ProjTwist.framesCocycle
#print axioms ArithDyn.Extension.ProjTwist.frame_coordinates_change
#print axioms ArithDyn.Extension.ProjTwist.reconstructionSections
#print axioms ArithDyn.Extension.ProjTwist.reconstructionSections_bijective
#print axioms ArithDyn.Extension.ProjTwist.reconstructionLinearEquiv
#print axioms ArithDyn.Extension.ProjTwist.reconstructFromFramesIso
#print axioms ArithDyn.Extension.ProjTwist.framesCocycle_eq
#print axioms ArithDyn.Extension.ProjTwist.reconstructWithCocycleIso
#print axioms ArithDyn.Extension.ProjTwist.pullbackTwistedIso
#print axioms ArithDyn.Extension.ProjTwist.pullbackComparison_local_identity
#print axioms ArithDyn.Extension.ProjTwist.regrading_pullRegular_coordinateRatio
#print axioms ArithDyn.Extension.ProjTwist.regrading_pullbackCocycle
#print axioms ArithDyn.Extension.ProjTwist.constantWeightTwistPullbackIso
#print axioms ArithDyn.Extension.ProjTwist.polarizationSectionEquiv
#print axioms ArithDyn.Extension.ProjTwist.polarizationUnit
#print axioms ArithDyn.Extension.ProjTwist.polarizationUnit_naturality
#print axioms ArithDyn.Extension.ProjTwist.polarizationUnit_overlap
#print axioms ArithDyn.Extension.ProjTwist.crossPowerCoefficient_change
#print axioms ArithDyn.Extension.ProjTwist.powerOnSource_independent
#print axioms ArithDyn.Extension.ProjTwist.existsUnique_globalPowerSections
#print axioms ArithDyn.Extension.ProjTwist.globalPowerSections
#print axioms ArithDyn.Extension.ProjTwist.globalPowerSections_coefficient
#print axioms ArithDyn.Extension.ProjTwist.globalPowerLinearMap
#print axioms ArithDyn.Extension.ProjTwist.globalPowerSections_restrict
#print axioms ArithDyn.Extension.ProjTwist.globalPowerSections_mul_apply
#print axioms ArithDyn.Extension.ProjTwist.globalPowerSections_zero_one_apply
#print axioms ArithDyn.Extension.ProjTwist.globalPowerSections_one_apply
#print axioms ArithDyn.Extension.ProjTwist.globalPowerModuleHom
#print axioms ArithDyn.Extension.ProjTwist.globalPowerSections_eq_local
#print axioms ArithDyn.Extension.ProjTwist.globalPowerModuleHom_isIso
#print axioms ArithDyn.Extension.ProjTwist.globalPowerModuleIso
#print axioms ArithDyn.Extension.ProjTwist.polarizationCocycleIso
#print axioms ArithDyn.Extension.ProjTwist.polarizationPowerIso
