/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.VonNeumannApproximationLowerBound
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Short-chain zero-bond test and axiom audits for the half-error entropy bounds. -/

open TNLean.MPS.AreaLaw

example {L q : ℕ} (hL : L ≤ 1) (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (hψ : ‖ψ‖ = 1) {a b : ℕ} (hab : a ≤ b) :
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q)
      (leftBlock L b \ leftBlock L a) ψ ≤ Real.log 2 := by
  have hMPS : IsOpenMPS L q 0 (fun x ↦ ψ x) := by
    apply (isOpenMPS_iff_internal_cutMatrix_rank_le ψ).mpr
    intro k hk0 hkL
    omega
  have hb := hMPS.regionEntropy_sdiff_leftBlock_le_two_log_add_half_error hψ hab
    (δ := 0) (by norm_num) (by simp)
  simpa using hb

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``IsOpenMPS.regionEntropy_leftBlock_le_log_add_half_error,
      ``IsOpenMPS.regionEntropy_sdiff_leftBlock_le_two_log_add_half_error] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
