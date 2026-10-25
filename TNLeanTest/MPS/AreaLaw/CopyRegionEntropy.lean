/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CopyRegionEntropy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Empty-block regressions, the four-bit application, and standard-axiom checks. -/

open TNLean.MPS.AreaLaw

-- Zero-length blocks remain valid even when the local dimension is zero.
example (η : EuclideanSpace ℂ (Fin 0 → Fin 0)) (hn : ‖η‖ = 1) (K a b : ℕ) :
    Entropy.regionEntropy (interval (K * 0) a b)
      (copyProduct (fun _ : Fin K ↦ η)) ≤ 0 := by
  have hB : ∀ R : Finset (Fin 0), Entropy.regionEntropy R η ≤ 0 := by
    intro R
    have hR : R = ∅ := Subsingleton.elim _ _
    rw [hR, Entropy.regionEntropy_eq_entropy, FiniteProduct.entropy_empty _ _ hn]
  simpa using regionEntropy_interval_copyProduct_le hn hB K a b

-- The single-copy two-bit bound gives the source's four-bit bound.
example {L q : ℕ} {η : EuclideanSpace ℂ (Fin L → Fin q)} (hn : ‖η‖ = 1)
    (hB : ∀ R : Finset (Fin L), Entropy.regionEntropy R η ≤ 2 * Real.log 2)
    (K a b : ℕ) :
    Entropy.regionEntropy (interval (K * L) a b)
      (copyProduct (fun _ : Fin K ↦ η)) ≤ 4 * Real.log 2 := by
  have h := regionEntropy_interval_copyProduct_le hn hB K a b
  linarith

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``TNLean.MPS.AreaLaw.regionState_copyProduct,
    ``TNLean.MPS.AreaLaw.regionEntropy_copyProduct,
    ``TNLean.MPS.AreaLaw.regionEntropy_copyRegions_le_sum,
    ``TNLean.MPS.AreaLaw.regionEntropy_interval_copyProduct_le]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
