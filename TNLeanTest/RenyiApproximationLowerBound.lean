/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.RenyiApproximationLowerBound
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audit for the finite-chain Rényi approximation bound. -/

open scoped ComplexOrder
open TNLean.MPS.AreaLaw

-- Internal cuts are absent on chains of length at most one; the bond budget
-- may therefore be zero even for a nonzero approximating vector.
example {L q : ℕ} (hL : L ≤ 1) {ψ φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : ‖ψ‖ = 1) {a b : ℕ} (hab : a ≤ b) {α δ : ℝ}
    (hα : 1 < α) (hδ : δ < 1)
    (herror : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) ≤ δ) :
    renyiEntropy (Entropy.regionState (n := fun _ : Fin L ↦ q)
      (leftBlock L b \ leftBlock L a) ψ)
      (Entropy.regionState_posSemidef _ _).isHermitian α +
      α / (α - 1) * Real.log (1 - δ) ≤ 0 := by
  have hφ : IsOpenMPS L q 0 (fun x ↦ φ x) :=
    (isOpenMPS_iff_internal_cutMatrix_rank_le φ).mpr (by intro k hk0 hkL; omega)
  simpa using hφ.renyiEntropy_sdiff_leftBlock_add_log_error_le_two_log hψ hab hα hδ herror

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``TNLean.MPS.AreaLaw.IsOpenMPS.rank_regionState_leftBlock_le,
    ``TNLean.MPS.AreaLaw.rectangularTraceNorm_regionState_leftBlock_sub_le,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.renyiEntropy_leftBlock_add_log_error_le_log,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.rank_regionState_sdiff_leftBlock_le_sq,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.rank_regionState_leftBlock_le_max,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.rank_regionState_sdiff_leftBlock_le_max_sq,
    ``TNLean.MPS.AreaLaw.IsOpenMPS.renyiEntropy_sdiff_leftBlock_add_log_error_le_two_log]
  for decl in decls do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
