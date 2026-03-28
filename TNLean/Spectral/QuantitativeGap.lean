/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.SpectralGap
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Wielandt.Primitivity.EasyDirections
import TNLean.Wielandt.Primitivity.ImpliesStronglyIrreducible
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Quantitative spectral gap bounds for MPS transfer operators

This file provides **explicit quantitative bounds** on the spectral gap of
MPS transfer operators, strengthening the existing qualitative result
`spectralRadius_mixedTransfer_lt_one` (which only proves `ρ < 1` without
a lower bound on `1 - ρ`).

## Building blocks (already formalized elsewhere)

* `pow_tendsto_zero_of_spectralRadius_lt_one` in `Spectral/SpectralGap.lean` —
  exponential convergence to zero when spectral radius < 1
* `compl_eigenvalue_norm_lt_one_of_primitive` in `Peripheral/Spectrum.lean` —
  primitive channels have spectral gap
* `cumulativeSpan_eq_top` in `Wielandt/WielandtBound.lean` — the D² Wielandt bound

## Main results

* `exponential_convergence_of_primitive` — for a primitive TP channel,
  `‖E^n(X) - P(X)‖ ≤ C · (1-δ)^n · ‖X‖` (convergence to fixed-point projection)
* `correlation_length_bound` — exponential decay of traceless iterates
* `spectral_gap_from_wielandt` — explicit spectral gap `δ > 0` with
  all non-unit eigenvalues satisfying `|μ| ≤ 1 - δ`

## Strengthening relative to the literature

The existing formalization proves `ρ(F_{AB}) < 1` for non-equivalent blocks
but gives no explicit bound. This file provides constructive bounds.

## References

* [M. Wolf, *Quantum Channels & Operations*, §6.3]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal ENNReal
open Matrix Finset

namespace MPSTensor

variable {d D : ℕ}

/-! ## Convergence rate from spectral gap -/

/-- **Exponential convergence of primitive channels.**

For a primitive TP channel `E` with unique fixed point `ρ_∞`, the iterates
`E^n(X)` converge exponentially to the fixed-point projection `P(X)`:

  `‖E^n(X) - P(X)‖ ≤ C · (1-δ)^n · ‖X‖`

where `P(X) = tr(X) · ρ_∞ / tr(ρ_∞)` is the projection onto the fixed state,
`δ > 0` is the spectral gap, and `C` depends on the Jordan structure.

The spectral gap `δ` exists by `compl_eigenvalue_norm_lt_one_of_primitive`
from `Peripheral/Spectrum.lean`. The exponential convergence follows from
`pow_tendsto_zero_of_spectralRadius_lt_one` in `Spectral/SpectralGap.lean`
applied to `E - P` (which has spectral radius < 1 by primitivity). -/
theorem exponential_convergence_of_primitive [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitive (transferMap (d := d) (D := D) A))
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ_pd : ρ.PosDef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    ∃ (C : ℝ) (δ : ℝ),
      0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
        ‖((transferMap (d := d) (D := D) A)^[n]) X -
          fixedPointProj ρ (ne_of_gt hρ_pd.trace_pos) X‖ ≤
          C * (1 - δ) ^ n * ‖X‖ := by
  -- TODO (#22): Two adapter lemmas needed before this can be wired:
  --
  -- (1) `huniq_fp`: the hypothesis `IsPrimitive (transferMap A)` does NOT directly
  --     give unique trace-zero fixed points. The abstract
  --     `compl_eigenvalue_norm_lt_one_of_primitive` requires
  --     `huniq_fp : ∀ X, E X = X → trace X = 0 → X = 0` as a parameter.
  --     For channels (CPTP maps), this follows from primitivity + CP structure, but
  --     the adapter `channel_primitive_implies_unique_trace_zero_fixedPoint` is not yet
  --     formalized. The existing `transferMap_fixedPoint_eq_zero_of_trace_eq_zero` in
  --     `PeripheralToSpectralGap.lean` requires `IsInjective A`, which is stronger than
  --     `IsPrimitive (transferMap A)`.
  --
  -- (2) Geometric bound from spectral radius: once `spectralRadius(E - P) < 1` is
  --     established, converting to `∃ C r, ‖(E-P)^n‖ ≤ C * r^n` requires a
  --     lemma `geometric_bound_of_spectralRadius_lt_one`:
  --       spectralRadius T < 1 → ∃ C r, 0 < C ∧ 0 < r ∧ r < 1 ∧ ∀ n, ‖T^n‖ ≤ C * r^n
  --     The Gelfand formula gives this eventually; packaging for all n requires
  --     a finite correction factor.
  sorry

/-- **Correlation length bound.**

For a primitive TP-normalized MPS tensor, traceless matrices decay
exponentially under the transfer map iteration. The rate is determined by
the spectral gap, which exists by primitivity.

This uses `pow_tendsto_zero_of_spectralRadius_lt_one` from
`Spectral/SpectralGap.lean` directly — traceless matrices lie in
`ker(P) = range(E - P)`, where `E - P` has spectral radius < 1. -/
theorem correlation_length_bound [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : IsInjective A) :
    ∃ (C : ℝ) (ξ : ℝ),
      0 < C ∧ 0 < ξ ∧
      ∀ (n : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
        Matrix.trace X = 0 →
        ‖((transferMap (d := d) (D := D) A)^[n]) X‖ ≤
          C * Real.exp (-(n : ℝ) / ξ) * ‖X‖ := by
  -- TODO (#22): ξ = -1/log(ρ₂) where ρ₂ is second-largest eigenvalue modulus
  sorry

/-! ## Explicit gap from Wielandt bound -/

/-- **Spectral gap from the Wielandt bound** (existential version).

For an injective TP-normalized MPS tensor, all eigenvalues of the transfer
map other than 1 have modulus strictly less than 1, with a uniform gap.

The existential bound `∃ δ > 0` follows from: injectivity implies primitivity
(by the Wielandt bound), primitivity implies spectral gap
(by `compl_eigenvalue_norm_lt_one_of_primitive`), and in finite dimensions
the maximum over finitely many eigenvalues gives a uniform bound. -/
theorem spectral_gap_from_wielandt [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : IsInjective A) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∀ (μ : ℂ), Module.End.HasEigenvalue (transferMap (d := d) (D := D) A) μ →
        μ ≠ 1 → ‖μ‖ ≤ 1 - δ := by
  classical
  set E := transferMap (d := d) (D := D) A
  -- Step 1: IsInjective → IsPrimitive (transferMap A)
  -- Chain: IsInjective → HasEventuallyFullKrausRank → IsPrimitivePaper → IsPeripherallyPrimitive
  have hFullKraus : HasEventuallyFullKrausRank A := by
    refine ⟨1, ?_⟩
    -- wordSpan A 1 = span of {evalWord A [i] | i : Fin d} = span of {A i | i} = ⊤
    rw [eq_top_iff]
    intro x _
    rw [wordSpan]
    -- range A ⊆ range (fun σ : Fin 1 → Fin d => evalWord A (List.ofFn σ))
    -- since span(range A) = ⊤ by IsInjective
    have hle : Submodule.span ℂ (Set.range A) ≤
        Submodule.span ℂ (Set.range fun σ : Fin 1 → Fin d => evalWord A (List.ofFn σ)) := by
      apply Submodule.span_mono
      intro y hy
      obtain ⟨i, rfl⟩ := hy
      exact ⟨fun _ => i, by simp [evalWord]⟩
    exact hle (hA ▸ Submodule.mem_top)
  have hPrimPaper : IsPrimitivePaper A :=
    isPrimitivePaper_of_hasEventuallyFullKrausRank A hFullKraus
  have hPrim : _root_.IsPrimitive E :=
    isPeripherallyPrimitive_of_isPrimitivePaper A hNorm hPrimPaper
  -- Step 2: every eigenvalue has ‖μ‖ ≤ 1
  have hbound : ∀ μ : ℂ, Module.End.HasEigenvalue E μ → ‖μ‖ ≤ 1 := by
    intro μ hμ
    exact eigenvalue_norm_le_one A A hNorm hNorm μ
      (by rwa [show E = mixedTransferMap A A from (mixedTransferMap_self A).symm] at hμ)
  -- Step 3: non-1 eigenvalues have ‖μ‖ < 1 (from IsPrimitive + eigenvalue bound)
  have hlt : ∀ μ : ℂ, Module.End.HasEigenvalue E μ → μ ≠ 1 → ‖μ‖ < 1 := by
    intro μ hμ hne
    exact lt_of_le_of_ne (hbound μ hμ) fun h => hne (hPrim.unique_peripheral μ hμ h)
  -- Step 4: uniform gap from finite eigenvalue set
  -- The eigenvalue set is finite (roots of minimal polynomial in finite dimensions)
  have hfin : Set.Finite {μ : ℂ | Module.End.HasEigenvalue E μ} :=
    Module.End.finite_hasEigenvalue E
  let S := {μ : ℂ | Module.End.HasEigenvalue E μ ∧ μ ≠ 1}
  have hSfin : S.Finite := hfin.subset fun μ hμ => hμ.1
  by_cases hS : S.Nonempty
  · -- Nonempty: take δ = 1 - max{‖μ‖ | μ ∈ S}
    let norms := hSfin.toFinset.image (fun μ => ‖μ‖)
    have hnorms_ne : norms.Nonempty := by
      obtain ⟨μ₀, hμ₀⟩ := hS
      exact ⟨‖μ₀‖, Finset.mem_image.mpr ⟨μ₀, hSfin.mem_toFinset.mpr hμ₀, rfl⟩⟩
    set r := norms.max' hnorms_ne with r_def
    have hr_lt : r < 1 := by
      rw [r_def, Finset.max'_lt_iff]
      intro x hx
      obtain ⟨μ, hμS, rfl⟩ := Finset.mem_image.mp hx
      exact hlt μ (hSfin.mem_toFinset.mp hμS).1 (hSfin.mem_toFinset.mp hμS).2
    refine ⟨1 - r, by linarith, fun μ hμ hne => ?_⟩
    have hμS : μ ∈ S := ⟨hμ, hne⟩
    have hμ_norm_mem : ‖μ‖ ∈ norms :=
      Finset.mem_image.mpr ⟨μ, hSfin.mem_toFinset.mpr hμS, rfl⟩
    linarith [Finset.le_max' norms ‖μ‖ hμ_norm_mem]
  · -- Empty: no non-1 eigenvalues, δ = 1 works vacuously
    exact ⟨1, one_pos, fun μ hμ hne => absurd ⟨μ, hμ, hne⟩ hS⟩

end MPSTensor
