/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousExactPreparation

/-!
# Preparation without normal-gauge construction

The noninjective, inhomogeneous exact-preparation theorem and normalized periodic states
are available through the algebraic preparation imports alone.
-/

open MPSTensor MPSPreparation QuantumCircuit

-- Inspect the compiled environment, rather than just direct source imports.
run_cmd do
  for name in (← Lean.getEnv).header.moduleNames do
    if name == `TNLean.MPS.CanonicalForm.NormalTensorGauge ||
        name == `TNLean.MPS.Preparation.ApproximatingState ||
        name == `TNLean.MPS.Preparation.FixedPointPairs ||
        name == `TNLean.MPS.Preparation.DepthUpperBound ||
        (`Gametheory).isPrefixOf name then
      throwError "Unexpected convergence dependency: {name}"

example {d D N : ℕ} (A : MPSTensor d D) (h : mpvState A N = 0) :
    normalizedMPVState A N = 0 := by
  simp [normalizedMPVState, h]

example {d D N : ℕ} (A : MPSTensor d D) (h : mpvState A N ≠ 0) :
    ‖normalizedMPVState A N‖ = 1 :=
  norm_normalizedMPVState h

-- No block-injectivity or normality hypothesis is added to the physical endpoint.
example (d D : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, ∀ (N : ℕ) [NeZero N] (A : MPSChainTensor d D N), chainState A ≠ 0 →
      ∃ T : ℕ, T ≤ C * N ∧
        IsPreparedInDepth T (fun s => ((‖chainState A‖ : ℂ)⁻¹ • chainState A) s) :=
  exists_isPreparedInDepth_normalizedChainState d D hd
