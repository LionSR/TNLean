/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.Transfer
import QICLean.Channel.ChoiDoeblin
import TNLean.MPS.Preparation.PositivePartRate

/-!
# Uniform contraction along an inhomogeneous chain

A common lower bound on the Choi matrices of the actual site maps gives a uniform exponential
contraction for their ordered products. The sites may themselves be fixed-length contiguous
blocks. Separate spectral gaps of the individual maps are not used: they do not control
products of different maps.

The contraction step reuses the quantum Doeblin theorem from QICLean. Its tensor interpretation
uses the exact transfer map of the blocked chain, not a power of any one site map.

## Main result

* `MPSChainTensor.traceNorm_transferMap_blockTensor_sub_le_of_choi_domination`: a uniform
  `n`-step trace-distance contraction derived from actual Choi domination.

## References

* Wolf, *Quantum Channels & Operations*, Theorem 8.17 (quantum Doeblin).
* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace MPSChainTensor

variable {d D n : ℕ}

/-- The blocked chain has a trace-preserving transfer map when every site map does. -/
theorem trace_transferMap_blockTensor (A : MPSChainTensor d D n)
    (hA : ∀ i, IsTracePreservingMap (Kraus.transferMap (A i)))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    (Kraus.transferMap (blockTensor A) X).trace = X.trace := by
  induction n with
  | zero => simp [transferMap_blockTensor]
  | succ n ih =>
    rw [transferMap_blockTensor, List.ofFn_succ, List.prod_cons]
    change (Kraus.transferMap (A 0)
      (((List.ofFn fun i => Kraus.transferMap (A i.succ)).prod) X)).trace = _
    rw [hA 0, ← transferMap_blockTensor]
    exact ih _ (fun i => hA i.succ)

/-- **Uniform Doeblin contraction on a chain.** If every site's normalized Choi matrix
uniformly dominates `ε/D` times `σ ⊗ I`, where `σ` is a density matrix and `0 ≤ ε ≤ 1`,
then the transfer map of the whole `n`-site block contracts the trace distance of density
matrices by at least the factor `(1 - ε)^n`. No translation invariance is assumed.

When each site is a fixed-length contiguous block, the condition is imposed on those actual
blocks, not on powers of the individual microscopic site maps. -/
theorem traceNorm_transferMap_blockTensor_sub_le_of_choi_domination
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (A : MPSChainTensor d D n)
    (hA : ∀ i, IsTracePreservingMap (Kraus.transferMap (A i)))
    (hchoi : ∀ i, ChoiRectangular.choiMatrix (Kraus.transferMap (A i)) ≥
      ((ε : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)))
    {ρ₁ ρ₂ : Matrix (Fin D) (Fin D) ℂ} (h₁ : ρ₁.PosSemidef)
    (h₂ : ρ₂.PosSemidef) (h₁tr : ρ₁.trace = 1) (h₂tr : ρ₂.trace = 1) :
    traceNorm (Kraus.transferMap (blockTensor A) ρ₁ -
      Kraus.transferMap (blockTensor A) ρ₂) ≤
      (1 - ε) ^ n * traceNorm (ρ₁ - ρ₂) := by
  induction n with
  | zero => simp [transferMap_blockTensor]
  | succ n ih =>
    let B : MPSChainTensor d D n := fun i => A i.succ
    have hB : ∀ i, IsTracePreservingMap (Kraus.transferMap (B i)) := fun i => hA i.succ
    have hhead : Kraus.transferMap (blockTensor A) =
        Kraus.transferMap (A 0) * Kraus.transferMap (blockTensor B) := by
      rw [transferMap_blockTensor, transferMap_blockTensor, List.ofFn_succ, List.prod_cons]
    rw [hhead]
    change traceNorm (Kraus.transferMap (A 0) (Kraus.transferMap (blockTensor B) ρ₁) -
      Kraus.transferMap (A 0) (Kraus.transferMap (blockTensor B) ρ₂)) ≤ _
    have hstep := traceNorm_map_sub_map_le_of_choi_domination (hA 0)
      (fun X hX => isHermitian_map_of_positive
        (fun Y hY => Kraus.transferMap_pos (A 0) hY) hX)
      hσ.isHermitian htr hε (hchoi 0)
      (Kraus.transferMap_pos (blockTensor B) h₁)
      (Kraus.transferMap_pos (blockTensor B) h₂)
      ((trace_transferMap_blockTensor B hB ρ₁).trans h₁tr)
      ((trace_transferMap_blockTensor B hB ρ₂).trans h₂tr)
    have htail := ih B hB (fun i => hchoi i.succ)
    calc _ ≤ (1 - ε) * traceNorm (Kraus.transferMap (blockTensor B) ρ₁ -
        Kraus.transferMap (blockTensor B) ρ₂) := hstep
      _ ≤ (1 - ε) * ((1 - ε) ^ n * traceNorm (ρ₁ - ρ₂)) :=
        mul_le_mul_of_nonneg_left htail (sub_nonneg.mpr hε1)
      _ = _ := by rw [pow_succ]; ring

end MPSChainTensor
