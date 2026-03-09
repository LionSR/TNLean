/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.SpectralGap

/-!
# Cross-correlation decay and block separation

Combining the iterated transfer formula with the spectral convergence,
we get the quantitative block separation statement: the MPV
cross-correlations between distinct blocks decay exponentially.

## Main results

* `cross_correlation_tendsto_zero`: cross-correlations between distinct
  blocks vanish as system size → ∞
* `self_correlation_persists`: self-correlations are preserved by
  the transfer operator

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac,
  *Matrix Product State Representations*, 2007.
-/

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D : ℕ}

section BlockSeparation

/-- **Cross-correlation decay**: For injective MPS tensors `A` and `B`
that are not gauge-phase equivalent, the cross-correlation
$$\sum_\sigma \mathrm{tr}(\mathrm{evalWord}(A,\sigma) \cdot X \cdot
  \mathrm{evalWord}(B,\sigma)^\dagger)$$
converges to zero as the system size `N → ∞`.

This is the trace of `F_{AB}^N(X)`, which tends to zero since
`F_{AB}^N(X) → 0` by `mixedTransfer_pow_tendsto_zero`. -/
theorem cross_correlation_tendsto_zero
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto
      (fun N => Matrix.trace (((mixedTransferMap A B) ^ N) X))
      Filter.atTop (nhds 0) := by
  -- Compose: F^N(X) → 0 (by spectral gap) and trace is continuous.
  have h := mixedTransfer_pow_tendsto_zero A B hA hB hA_norm hB_norm hAB X
  have h_cont : Continuous (Matrix.traceLinearMap (Fin D) ℂ ℂ) :=
    LinearMap.continuous_of_finiteDimensional _
  have h2 : Filter.Tendsto
      (fun N => (Matrix.traceLinearMap (Fin D) ℂ ℂ) (((mixedTransferMap A B) ^ N) X))
      Filter.atTop (nhds 0) := by
    rw [← map_zero (Matrix.traceLinearMap (Fin D) ℂ ℂ)]
    exact h_cont.continuousAt.tendsto.comp h
  simpa [Matrix.traceLinearMap_apply] using h2

/-- **Self-correlation persists**: If `ρ` is a fixed point of `E_A`, then
`tr(E_A^N(ρ)) = tr(ρ)` for all `N`. This is the diagonal counterpart to
the off-diagonal decay: self-terms persist while cross-terms vanish. -/
theorem self_correlation_persists
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hfp : transferMap (d := d) (D := D) A ρ = ρ) :
    ∀ N : ℕ,
      Matrix.trace (((transferMap (d := d) (D := D) A) ^ N) ρ) = Matrix.trace ρ := by
  intro N
  suffices hfix : ((transferMap (d := d) (D := D) A) ^ N) ρ = ρ by rw [hfix]
  induction N with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, hfp]


end BlockSeparation

end MPSTensor
