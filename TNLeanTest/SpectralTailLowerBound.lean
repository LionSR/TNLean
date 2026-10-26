/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.SpectralTailLowerBound
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Exact approximation and the unit-error boundary of the chain spectral-tail bound. -/

open TNLean.MPS.AreaLaw
open scoped ComplexOrder

-- Exact approximation gives zero discarded mass without a positive-budget premise.
example {L q D : ℕ} (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (hψ : ‖ψ‖ = 1) (hMPS : IsOpenMPS L q D (fun x ↦ ψ x))
    {k : ℕ} (hk0 : 0 < k) (hkL : k < L) :
    ∑ i ∈ Finset.Ico D (Fintype.card (Entropy.RegionConfig (fun _ : Fin L ↦ q)
      (leftBlock L k))),
      (Entropy.regionState_posSemidef (leftBlock L k) ψ).isHermitian.descEigenvalue i ≤ 0 := by
  simpa using hMPS.sum_descEigenvalue_leftBlock_tail_le_traceNorm hψ hk0 hkL

-- The zero approximant is an actual MPS with bond budget zero; its error is one.
example {L q : ℕ} (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (hψ : ‖ψ‖ = 1) {k : ℕ} (hk0 : 0 < k) (hkL : k < L) :
    ∑ i ∈ Finset.Ico 0 (Fintype.card (Entropy.RegionConfig (fun _ : Fin L ↦ q)
      (leftBlock L k))),
      (Entropy.regionState_posSemidef (leftBlock L k) ψ).isHermitian.descEigenvalue i ≤ 1 := by
  have hz : IsOpenMPS L q 0 (fun x ↦ (0 : EuclideanSpace ℂ (Fin L → Fin q)) x) := by
    apply (isOpenMPS_iff_internal_cutMatrix_rank_le _).mpr
    intro j _ _
    change (0 : Matrix _ _ ℂ).rank ≤ 0
    simp
  have ht := hz.sum_descEigenvalue_leftBlock_tail_le_traceNorm hψ hk0 hkL
  have hzouter : Matrix.euclideanOuterProduct (0 : EuclideanSpace ℂ (Fin L → Fin q)) 0 =
      (0 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) := by
    simp [Matrix.euclideanOuterProduct]
  simpa only [hzouter, sub_zero, Matrix.rectangularTraceNorm_euclideanOuterProduct_self,
    hψ, one_pow] using ht

run_cmd do
  let decl := ``TNLean.MPS.AreaLaw.IsOpenMPS.sum_descEigenvalue_leftBlock_tail_le_traceNorm
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
