/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OverlappingLogLogPreparation

/-! Regression checks for the all-length canonical capstone and complex sector cancellation.

## References

* arXiv:2307.01696, Supplemental Material, eqs. (S2)--(S4), and
  "Long-range MPS using measurements".
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped BigOperators ComplexOrder InnerProductSpace

-- The constant is selected before both accuracy and chain length.
example
    {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    (hneq : ∀ j j', j ≠ j' → ∀ h : Dj j = Dj j',
      ¬ GaugePhaseEquiv (h ▸ Aj j) (Aj j')) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], 2 ≤ N →
      mpvState (repeatedBlockSum Aj ι μ) N ≠ 0 →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log (Real.log (N / ε) + 1) ∧
        IsPreparedWithMeasurementRoundsInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, normalizedMPVState (repeatedBlockSum Aj ι μ) N⟫_ℂ‖ ≤ ε :=
  exists_isPreparedWithMeasurementRoundsInDepth_repeatedBlockSum_le_log_log_of_inequivalent
    hι hdisj μ hN hA hσ htr hfix hneq

-- Different bond dimensions need no equal-dimension gauge comparison.
example {d : ℕ} (A : MPSTensor d 2) (B : MPSTensor d 3)
    (hA : Kraus.IsNormal A) (hB : Kraus.IsNormal B)
    (hAL : IsLeftCanonical A) (hBL : IsLeftCanonical B) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Kraus.mixedMapLM A B) μ) : ‖μ‖ < 1 :=
  mixedMap_eigenvalue_norm_lt_one_of_normal_inequivalent A B hA hB hAL hBL
    (fun h => by omega) hμ

private def cancellationWeights : CopyWeights 2 (fun _ => 2) where
  weight j k := if j = 0 then if k = 0 then 1 else Complex.I else 1
  mult_pos _ := by decide
  weight_ne_zero j k := by
    fin_cases j <;> fin_cases k <;> norm_num

-- Genuine complex phases cancel a whole sector at N = 2, without cancelling the others.
example : bntWeight cancellationWeights 2 0 = 0 ∧ bntWeight cancellationWeights 2 1 = 2 := by
  norm_num [bntWeight, cancellationWeights, Fin.sum_univ_two]

private def productSector (j : Fin 2) : MPSTensor 2 1 := fun i _ _ => if i = j then 1 else 0

-- The total periodic combination is nonzero despite that vanishing individual amplitude.
example : (∑ j : Fin 2, bntWeight cancellationWeights 2 j • mpvState (productSector j) 2) ≠ 0 := by
  intro hzero
  have h := congrArg (fun v : MPVSpace 2 2 => v (fun _ => 1)) hzero
  norm_num [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    bntWeight, cancellationWeights, productSector, mpvState_apply, mpv, Kraus.evalWord,
    List.ofFn_succ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] at h
