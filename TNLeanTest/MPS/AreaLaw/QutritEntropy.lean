/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.QutritEntropy
import Mathlib.Tactic.NormNum
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Arbitrary regions and boundary probabilities of the qutrit family

The entropy bound applies to disconnected regions, both boundary probabilities,
and the empty and full chain. The source's inverse-length specialization also
includes `N = 1`.
-/

open TNLean.MPS.AreaLaw.EntropyScaling

example : Entropy.regionEntropy ({0, 2} : Finset (Fin (2 + 2))) (qutritState 2 (1 / 3)) ≤
    Real.binEntropy (1 / 3) + (1 / 3) * 2 * Real.log 2 :=
  regionEntropy_qutritState_le (by decide) _ (by norm_num) (by norm_num)

example (A : Finset (Fin (2 + 2))) :
    Entropy.regionEntropy A (qutritState 2 0) ≤ 0 := by
  simpa using regionEntropy_qutritState_le (N := 2) (by decide) A
    (p := 0) (by norm_num) (by norm_num)

example (A : Finset (Fin (2 + 2))) :
    Entropy.regionEntropy A (qutritState 2 1) ≤ 2 * Real.log 2 := by
  simpa using regionEntropy_qutritState_le (N := 2) (by decide) A
    (p := 1) (by norm_num) (by norm_num)

example : Entropy.regionEntropy ∅ (qutritState 2 (1 / 3)) = 0 :=
  regionEntropy_qutritState_empty (by decide) (by norm_num) (by norm_num)

example : Entropy.regionEntropy Finset.univ (qutritState 2 (1 / 3)) = 0 :=
  regionEntropy_qutritState_univ (by decide) (by norm_num) (by norm_num)

example (A : Finset (Fin (1 + 1))) :
    Entropy.regionEntropy A (qutritFamily 1) ≤ 2 * Real.log 2 :=
  regionEntropy_qutritFamily_le (by decide) A

example : Entropy.regionState ({0, 2} : Finset (Fin (2 + 2))) (qutritState 2 (1 / 3)) =
    ((1 - 1 / 3 : ℝ) : ℂ) • Entropy.regionState ({0, 2} : Finset (Fin (2 + 2)))
      (qutritState 2 0) +
    ((1 / 3 : ℝ) : ℂ) • Entropy.regionState ({0, 2} : Finset (Fin (2 + 2)))
      (qutritState 2 1) :=
  regionState_qutritState_decomposition (by decide) (by norm_num) (by norm_num)

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``TNLean.MPS.AreaLaw.EntropyScaling.regionState_qutritState_decomposition,
    ``TNLean.MPS.AreaLaw.EntropyScaling.regionEntropy_qutritState_le,
    ``TNLean.MPS.AreaLaw.EntropyScaling.regionEntropy_qutritState_empty,
    ``TNLean.MPS.AreaLaw.EntropyScaling.regionEntropy_qutritState_univ,
    ``TNLean.MPS.AreaLaw.EntropyScaling.regionEntropy_qutritFamily_le]
  for decl in names do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
