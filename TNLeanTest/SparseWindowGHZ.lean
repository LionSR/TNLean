/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SparseWindowGHZ

/-! Regression checks for sparse coherent labels, singleton rings and mixed block parities.

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
* arXiv:2103.13367, Example 1.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped BigOperators

-- One depth bound works for every singleton length, including odd lengths.
example : ∃ C : ℕ, ∀ n (hn : 6 ≤ n), ∀ α : Cfg 2 2 → ℂ, ∑ u, star (α u) * α u = 1 →
    let : NeZero n := ⟨by omega⟩
    IsPreparedWithMeasurementRoundsInDepth C
      (windowGHZState (N := n) (ℓ := fun _ : Fin 1 => n) (by simp) (fun _ => by omega) α) := by
  obtain ⟨C, hC⟩ := exists_isPreparedWithMeasurementRoundsInDepth_windowGHZState (d := 2)
    (r := 2) (by omega)
  refine ⟨C, fun n hn α hα => ?_⟩
  let : NeZero n := ⟨by omega⟩
  exact hC (fun _ : Fin 1 => n) (N := n) (by simp) (fun _ => by omega) (fun _ => by omega) α hα

-- The lengths may vary independently and carry every parity pattern around the ring.
example : ∃ C : ℕ, ∀ b : Fin 4 → Fin 2, ∀ α : Cfg 2 2 → ℂ,
    ∑ u, star (α u) * α u = 1 →
    let ℓ := fun k => 6 + (b k).val
    let N := ∑ k, ℓ k
    let : NeZero N := ⟨by dsimp [N, ℓ]; positivity⟩
    IsPreparedWithMeasurementRoundsInDepth C
      (windowGHZState (ℓ := ℓ) (N := N) rfl (fun _ => by dsimp [ℓ]; omega) α) := by
  obtain ⟨C, hC⟩ := exists_isPreparedWithMeasurementRoundsInDepth_windowGHZState (d := 2)
    (r := 2) (by omega)
  refine ⟨C, fun b α hα => ?_⟩
  dsimp only
  let : NeZero (∑ k, (6 + (b k).val)) := ⟨by positivity⟩
  exact hC (fun k => 6 + (b k).val) rfl (fun _ => by omega) (fun _ => by omega) α hα

-- Coherence is explicit: the final correction's scalar is selected before the amplitudes.
example {M N r : ℕ} [NeZero M] [NeZero N] {ℓ : Fin M → ℕ}
    (hN : ∑ k, ℓ k = N) (hr : ∀ k, r + r ≤ ℓ k) :
    ∃ R : MeasurementRound 2 N, R.depth = 0 ∧ ∀ m, ∃ c : ℂ, ∀ α : Cfg 2 r → ℂ,
      R.kraus m *ᵥ windowGHZDifference hN hr α = c • windowGHZState hN hr α :=
  exists_windowGHZCorrectionRound hN hr

-- A fixed teleportation history has the same scalar on every coherent input with zero scratch.
example {M N r : ℕ} [NeZero N] {ℓ : Fin M → ℕ} (hr : 2 ≤ r)
    (hN : ∑ k, ℓ k = N) (hℓ : ∀ k, 3 * r ≤ ℓ k) :
    ∃ Rs : List (MeasurementRound 2 N),
      ∀ m : MeasurementRound.OutcomeHistory Rs, ∃ c : ℂ,
        ∀ v : Cfg 2 N → ℂ, IsZeroOn (windowCentralSites hN r) v →
          MeasurementRound.historyKraus Rs m *ᵥ v = c •
            (blockLayerOp hN (fun k => embedOp (SparseRegister.ends (by have := hℓ k; omega))
              ((tailShift r).permMatrix ℂ)) *ᵥ v) := by
  obtain ⟨C, hC⟩ := exists_rounds_sparseBlockShift (d := 2) hr
  obtain ⟨Rs, -, -, hc⟩ := hC hN hℓ
  exact ⟨Rs, hc⟩
