/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TwoMarkerMiddleFactors
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of prescribed middle-factor coefficients -/

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``Matrix.exists_left_factors_of_operatorBlock_mem_span,
    ``Matrix.exists_right_factors_of_left_blocks_mem_span,
    ``TNLean.MPS.AreaLaw.TwoMarkerMiddleIndex,
    ``TNLean.MPS.AreaLaw.twoMarkerMiddleFactor,
    ``TNLean.MPS.AreaLaw.twoMarkerCoefficient,
    ``TNLean.MPS.AreaLaw.operatorBlock_sum,
    ``TNLean.MPS.AreaLaw.operatorBlock_kronecker_eq_smul,
    ``TNLean.MPS.AreaLaw.card_twoMarkerMiddleIndex_square_le,
    ``TNLean.MPS.AreaLaw.exists_sum_twoMarkerCoefficient_decomposition] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
