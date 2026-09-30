/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap
import QICLean.Channel.Peripheral.SpectralRadius
import TNLean.MPS.CanonicalForm.NormalReduction.TPGauge
import TNLean.MPS.Periodic.PeriodExistence

/-!
# Positive-weight periodic blocks for an arbitrary tensor

The irreducible decomposition of arXiv:1708.00029, Proposition `thm:irr`,
followed by its trace-preserving normalization `eq:unital`, gives periodic
left-canonical blocks with positive real weights. Equality is at positive
physical lengths; removing zero blocks can reduce the bond dimension.

This decomposition does not yet group repeated blocks into a basis, diagonalize
fixed points, or decompose the blocks after an arbitrary prescribed blocking.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.Operator Kraus

namespace MPSTensor

variable {d D : ℕ}

/-- Every irreducible left-canonical tensor of positive bond dimension has a period.
Source: arXiv:1708.00029, lines 248–258 and `eq:unital`; Wolf Proposition 6.1. -/
theorem exists_isPeriodic_of_irreducible_of_isLeftCanonical [NeZero D]
    (A : MPSTensor d D) (hIrr : Kraus.IsIrreducibleFamily A)
    (hA : IsLeftCanonical A) : ∃ m, IsPeriodic m A := by
  have hRad := (Kraus.isPositiveMap_mapLM A).spectralRadius_eq_one_of_tracePreserving
    (Kraus.isTracePreservingMap_mapLM_of_isTP A hA)
  obtain ⟨m, hm⟩ :=
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one hIrr hRad
  exact ⟨m, hIrr, hA, hm.period_pos, hm.peripheral_eq⟩

/-- An arbitrary tensor has the same positive-length MPVs as a direct sum of periodic
left-canonical tensors with strictly positive real weights and total bond dimension at most D.
Source: arXiv:1708.00029, Proposition `thm:irr`, lines 238–271, and `eq:unital`, lines 313–320.
No blocking of the physical sites is performed. -/
theorem exists_periodic_blockDecomposition (A : MPSTensor d D) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)) (period : Fin r → ℕ),
      (∀ k, IsPeriodic (period k) (blocks k)) ∧
      (∀ k, 0 < μ k) ∧ (∀ k, 0 < dim k) ∧
      SameMPV₂Pos A (toTensorFromBlocks (μ := μ) blocks) ∧
      ∑ k, dim k ≤ D := by
  obtain ⟨r, dim, μ, blocks, hIrr, hTP, hμ, hDim, hSame, hBound⟩ :=
    exists_tp_gauge_from_arbitrary A
  have hp : ∀ k, ∃ m, IsPeriodic m (blocks k) := by
    intro k
    let : NeZero (dim k) := ⟨Nat.ne_of_gt (hDim k)⟩
    exact exists_isPeriodic_of_irreducible_of_isLeftCanonical (blocks k) (hIrr k) (hTP k)
  choose period hperiod using hp
  exact ⟨r, dim, μ, blocks, period, hperiod, hμ, hDim, hSame, hBound⟩

end MPSTensor
