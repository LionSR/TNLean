/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Spectral.TransferOperatorGapInjective

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

* [CPGSV21] Cirac, Pérez-García, Schuch, Verstraete,
  *Matrix Product States and Projected Entangled Pair States*,
  Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.
  Sec. 2.3 (correlations and transfer matrix), Sec. 4 (transfer-matrix gap).
  Source: `Papers/2011.12127/`
* [PGWSVC08] Pérez-García, Wolf, Sanz, Verstraete, Cirac,
  *String order and symmetries in quantum spin lattices*,
  Phys. Rev. Lett. 100, 167202 (2008), arXiv:0802.0447.
  Source: `Papers/0802.0447/`
-/

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D : ℕ}

section BlockSeparation

/-- **Cross-correlation decay**: For injective MPS tensors `A` and `B`
that are not gauge-phase equivalent, the cross-correlation
$$\sum_\sigma \mathrm{tr}(\mathrm{Kraus.evalWord}(A,\sigma) \cdot X \cdot
  \mathrm{Kraus.evalWord}(B,\sigma)^\dagger)$$
converges to zero as the system size `N → ∞`.

This is the trace of `F_{AB}^N(X)`, which tends to zero since
`F_{AB}^N(X) → 0` by `mixedTransfer_pow_tendsto_zero`. -/
theorem cross_correlation_tendsto_zero
    (A B : MPSTensor d D)
    (hA : Kraus.IsInjective A) (hB : Kraus.IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto
      (fun N => Matrix.trace (((Kraus.mixedTransferMap A B) ^ N) X))
      Filter.atTop (nhds 0) := by
  have hK : ¬ Kraus.GaugePhaseEquiv A B :=
    fun h => hAB (gaugePhaseEquiv_of_krausGaugePhaseEquiv h)
  simpa [Kraus.mixedTransferMap] using
    Kraus.cross_correlation_tendsto_zero A B
      (Kraus.isIrreducibleMap_mapLM_of_transferMap A
        (Kraus.injective_implies_irreducibleCP A hA))
      (Kraus.isIrreducibleMap_mapLM_of_transferMap B
        (Kraus.injective_implies_irreducibleCP B hB))
      hA_norm hB_norm hK X

/-- **Self-correlation persists**: If `ρ` is a fixed point of `E_A`, then
`tr(E_A^N(ρ)) = tr(ρ)` for all `N`. This is the diagonal counterpart to
the off-diagonal decay: self-terms persist while cross-terms vanish. -/
theorem self_correlation_persists
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hfp : Kraus.transferMap (d := d) (D := D) A ρ = ρ) :
    ∀ N : ℕ,
      Matrix.trace (((Kraus.transferMap (d := d) (D := D) A) ^ N) ρ) = Matrix.trace ρ := by
  rw [← Kraus.mapLM_eq_transferMap] at hfp ⊢
  exact Kraus.self_correlation_persists A ρ hfp


end BlockSeparation

end MPSTensor
