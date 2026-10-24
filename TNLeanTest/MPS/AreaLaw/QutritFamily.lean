/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.QutritFamily
import Mathlib.Tactic.NormNum
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Boundary probabilities and the middle-cut spectrum of the qutrit family

Regression checks for arXiv:0705.0292v2, `eq:magicstate`, including zero Schmidt weights,
the explicit four-qutrit example and the actual chain marginal.
-/

open TNLean.MPS.AreaLaw.EntropyScaling
open Polynomial

-- Both probability endpoints are allowed, including zero Schmidt weights.
example : ‖qutritState 1 0‖ = 1 := norm_qutritState (by decide) (by norm_num) (by norm_num)
example : ‖qutritState 1 1‖ = 1 := norm_qutritState (by decide) (by norm_num) (by norm_num)

-- The first value in the range used for the counterexample is a normalized four-qutrit state.
example : ‖qutritFamily 2‖ = 1 := norm_qutritFamily (by decide)

-- At N = 2 the nine-dimensional marginal has four zero eigenvalues,
-- one weight 1/2 and four weights 1/8.
example : (qutritMiddleMarginal 2 (1 / 2)).charpoly =
    X ^ 4 * ((X - C (1 / 2 : ℂ)) * (X - C (1 / 8 : ℂ)) ^ 4) := by
  convert charpoly_qutritMiddleMarginal (N := 2) (by decide)
    (p := 1 / 2) (by norm_num) (by norm_num) using 1
  norm_num

-- The same spectrum belongs to the actual regional state on the first two sites.
example : (Entropy.regionState (n := fun _ : Fin (2 + 2) ↦ 3)
    (TNLean.MPS.AreaLaw.leftBlock (2 + 2) 2) (qutritState 2 (1 / 2))).charpoly =
    X ^ 4 * ((X - C (1 / 2 : ℂ)) * (X - C (1 / 8 : ℂ)) ^ 4) := by
  convert charpoly_regionState_qutritState (N := 2) (by decide)
    (p := 1 / 2) (by norm_num) (by norm_num) using 1
  norm_num

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``TNLean.MPS.AreaLaw.EntropyScaling.norm_qutritState,
    ``TNLean.MPS.AreaLaw.EntropyScaling.charpoly_qutritMiddleMarginal,
    ``TNLean.MPS.AreaLaw.EntropyScaling.charpoly_regionState_qutritState]
  for decl in names do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
