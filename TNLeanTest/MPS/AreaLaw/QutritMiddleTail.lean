/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.QutritMiddleTail
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Middle-cut mass of the qutrit family

Checks at zero bond, the first nontrivial family member, and bonds beyond
its physical dimension. Source: arXiv:0705.0292v2, lines 475–479.
-/

open TNLean.MPS.AreaLaw.EntropyScaling
open scoped ComplexOrder

-- At N=2, retaining only the flag discards at least half the mass.
example : (1 : ℝ) / 2 ≤
    1 - (qutritMiddleMarginal_posSemidef 2 (2 : ℝ)⁻¹).isHermitian.kyFanNorm 1 := by
  simpa using one_sub_kyFanNorm_qutritFamily_ge (N := 2) (by decide) 1

-- Zero bond is allowed and leaves all the mass.
example : 1 - (qutritMiddleMarginal_posSemidef 2 (2 : ℝ)⁻¹).isHermitian.kyFanNorm 0 = 1 :=
  one_sub_kyFanNorm_qutritMiddleMarginal_zero _ _

-- No hidden upper bound on D: 10 exceeds the physical dimension 3^2.
example : -(5 : ℝ) / 8 ≤
    1 - (qutritMiddleMarginal_posSemidef 2 (2 : ℝ)⁻¹).isHermitian.kyFanNorm 10 := by
  convert one_sub_kyFanNorm_qutritFamily_ge (N := 2) (by decide) 10 using 1
  norm_num

-- At p=0 the estimate still applies to the pure flag state.
example (D : ℕ) : (0 : ℝ) ≤
    1 - (qutritMiddleMarginal_posSemidef 2 0).isHermitian.kyFanNorm D := by
  simpa using one_sub_kyFanNorm_qutritMiddleMarginal_ge (N := 2) (by decide)
    (p := 0) (by norm_num) (by norm_num) (by norm_num) D

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``TNLean.MPS.AreaLaw.EntropyScaling.trace_projection_qutritMiddleMarginal_le,
    ``TNLean.MPS.AreaLaw.EntropyScaling.kyFanNorm_qutritMiddleMarginal_le,
    ``TNLean.MPS.AreaLaw.EntropyScaling.one_sub_kyFanNorm_qutritFamily_ge]
  for decl in names do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
