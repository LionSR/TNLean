/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularSpecialization
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact kernel-dependency guards for the native rectangular specialization -/

/-- info:
'TNLean.PEPS.AreaLaw.rectangleAreaLawSupport_injective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.rectangleAreaLawSupport_injective

/-- info:
'TNLean.PEPS.AreaLaw.RectangularHamiltonian.hermitianTerm_mem_supportedOperators'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.RectangularHamiltonian.hermitianTerm_mem_supportedOperators

/-- info:
'TNLean.PEPS.AreaLaw.RectangularHamiltonian.hermitianTerm_norm_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.RectangularHamiltonian.hermitianTerm_norm_le

/-- info:
'TNLean.PEPS.AreaLaw.RectangularHamiltonian.sum_hermitianTerm'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.RectangularHamiltonian.sum_hermitianTerm

/-- info:
'TNLean.PEPS.AreaLaw.RectangularHamiltonian.toAreaLawHamiltonian_operator'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.RectangularHamiltonian.toAreaLawHamiltonian_operator

/-- info:
'TNLean.PEPS.AreaLaw.RectangularHamiltonian.isGappedGroundState_toAreaLawHamiltonian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.RectangularHamiltonian.isGappedGroundState_toAreaLawHamiltonian

/-- info:
'TNLean.PEPS.AreaLaw.card_edgeBoundary_rectangular'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_edgeBoundary_rectangular

/-- info:
'TNLean.PEPS.AreaLaw.map_rectangleInnerBoundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.map_rectangleInnerBoundary

/-- info:
'TNLean.PEPS.AreaLaw.map_rectangleEndpointBoundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.map_rectangleEndpointBoundary

/-- info:
'TNLean.PEPS.AreaLaw.rectangleEdgeBoundary_card_le_four_mul_innerBoundary_card'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.rectangleEdgeBoundary_card_le_four_mul_innerBoundary_card

/-- info:
'TNLean.PEPS.AreaLaw.rectangleEdgeBoundary_card_le_two_mul_endpointBoundary_card'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.rectangleEdgeBoundary_card_le_two_mul_endpointBoundary_card

/-- info:
'TNLean.PEPS.AreaLaw.regionalEntropy_rectangleAreaLawState'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.regionalEntropy_rectangleAreaLawState

/-- info:
'TNLean.PEPS.AreaLaw.UniformAreaLaw.rectangularEntropyAreaLaw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.UniformAreaLaw.rectangularEntropyAreaLaw

/-- info:
'TNLean.PEPS.AreaLaw.RectangularEntropyAreaLaw.squareEntropyAreaLaw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.RectangularEntropyAreaLaw.squareEntropyAreaLaw

-- Every public declaration, including all source-model fields, must exist and
-- have no kernel dependencies outside the standard logical foundations.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.Approximation.SquareHamiltonian.toRectangularHamiltonian,
    ``TNLean.PEPS.AreaLaw.RectangleConfiguration,
    ``TNLean.PEPS.AreaLaw.RectangleInteraction,
    ``TNLean.PEPS.AreaLaw.RectangleStateSpace,
    ``TNLean.PEPS.AreaLaw.RectangularEntropyAreaLaw,
    ``TNLean.PEPS.AreaLaw.RectangularEntropyAreaLaw.squareEntropyAreaLaw,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.IsGappedGroundState,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.edgeTerm,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.edge_norm_le,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.edge_supported,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.hermitian,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.hermitianTerm,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.hermitianTerm_isHermitian,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.hermitianTerm_mem_supportedOperators,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.hermitianTerm_norm_le,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.isGappedGroundState_toAreaLawHamiltonian,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.operator,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.siteTerm,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.site_norm_le,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.site_supported,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.sum_hermitianTerm,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.toAreaLawHamiltonian,
    ``TNLean.PEPS.AreaLaw.RectangularHamiltonian.toAreaLawHamiltonian_operator,
    ``TNLean.PEPS.AreaLaw.UniformAreaLaw.rectangularEntropyAreaLaw,
    ``TNLean.PEPS.AreaLaw.card_edgeBoundary_rectangular,
    ``TNLean.PEPS.AreaLaw.card_endpointBoundary_rectangular,
    ``TNLean.PEPS.AreaLaw.card_innerBoundary_rectangular,
    ``TNLean.PEPS.AreaLaw.embedOp_rectangular_eq_reindex,
    ``TNLean.PEPS.AreaLaw.map_rectangleEndpointBoundary,
    ``TNLean.PEPS.AreaLaw.map_rectangleInnerBoundary,
    ``TNLean.PEPS.AreaLaw.mem_endpointBoundary_iff_adj,
    ``TNLean.PEPS.AreaLaw.norm_rectangleAreaLawState,
    ``TNLean.PEPS.AreaLaw.rectangleAreaLawState,
    ``TNLean.PEPS.AreaLaw.rectangleAreaLawSupport,
    ``TNLean.PEPS.AreaLaw.rectangleAreaLawSupport_injective,
    ``TNLean.PEPS.AreaLaw.rectangleEdgeBoundary_card_le_four_mul_innerBoundary_card,
    ``TNLean.PEPS.AreaLaw.rectangleEdgeBoundary_card_le_two_mul_endpointBoundary_card,
    ``TNLean.PEPS.AreaLaw.rectangleEndpointBoundary,
    ``TNLean.PEPS.AreaLaw.rectangleInnerBoundary,
    ``TNLean.PEPS.AreaLaw.rectangleInteractionSupport,
    ``TNLean.PEPS.AreaLaw.regionalEntropy_rectangleAreaLawState]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
